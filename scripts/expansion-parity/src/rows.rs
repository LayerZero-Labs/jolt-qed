//! Expansion through Jolt's production entry point and JSON rendering of
//! source instructions and final rows (schema in the I0 design note).
//!
//! Every derived row field comes from Jolt's own functions: circuit and
//! instruction flags from `jolt_riscv::Flags`, the lookup table from
//! `jolt_lookup_tables::InstructionLookupTable`, and the RAF flag from
//! `jolt_witness::witnesses::InstructionRafFlag::extract`.

use jolt_lookup_tables::{InstructionLookupTable, LookupTableKind};
use jolt_program::expand::{expand_instruction_with_provider, ExpansionAllocator, ExpansionError};
use jolt_program::preprocess::{BytecodePreprocessing, JoltProgramPreprocessing, RAMPreprocessing};
use jolt_riscv::{
    CircuitFlags, Flags, InstructionFlags, JoltInstruction, JoltInstructionKind,
    JoltInstructionProfile, JoltInstructionRow, JoltTraceRow, NormalizedOperands, RamAccess,
    RamRead, RamWrite, RegisterState, SourceInstruction, CIRCUIT_FLAGS, NUM_INSTRUCTION_FLAGS,
    RV64IMAC_JOLT, RV64IMAC_JOLT_ALL_INLINES,
};
use jolt_witness::witnesses::{Extract, InstructionRafFlag, WitnessEnv};
use serde_json::{json, Value};
use tracer::TracerInlineExpansionProvider;

/// Instruction flags in enum order. Jolt has no const array for them, so the
/// list is checked against `NUM_INSTRUCTION_FLAGS` at startup.
pub const INSTRUCTION_FLAGS: [InstructionFlags; 7] = [
    InstructionFlags::LeftOperandIsPC,
    InstructionFlags::RightOperandIsImm,
    InstructionFlags::LeftOperandIsRs1Value,
    InstructionFlags::RightOperandIsRs2Value,
    InstructionFlags::Branch,
    InstructionFlags::IsNoop,
    InstructionFlags::RightOperandIsRdWriteValue,
];

pub fn check_flag_lists() -> Result<(), String> {
    if INSTRUCTION_FLAGS.len() != NUM_INSTRUCTION_FLAGS {
        return Err(format!(
            "driver lists {} instruction flags, Jolt has {NUM_INSTRUCTION_FLAGS}",
            INSTRUCTION_FLAGS.len()
        ));
    }
    for (i, f) in INSTRUCTION_FLAGS.iter().enumerate() {
        if *f as usize != i {
            return Err(format!("instruction flag {f:?} is not at index {i}"));
        }
    }
    Ok(())
}

/// Expands one source instruction with the production provider and profile.
pub fn expand(
    source: &SourceInstruction,
    allocator: &mut ExpansionAllocator,
) -> Result<Vec<JoltInstructionRow>, ExpansionError> {
    expand_with_profile(source, allocator, RV64IMAC_JOLT_ALL_INLINES)
}

pub fn expand_with_profile(
    source: &SourceInstruction,
    allocator: &mut ExpansionAllocator,
    profile: JoltInstructionProfile,
) -> Result<Vec<JoltInstructionRow>, ExpansionError> {
    let mut provider = TracerInlineExpansionProvider::new();
    let out = expand_instruction_with_provider(source, allocator, &mut provider, profile)?;
    Ok(out.into_iter().map(JoltInstructionRow::from).collect())
}

/// The allocator check: `ExpansionAllocator` derives `Debug` and `Clone` but
/// not `PartialEq`, and its `Debug` output prints every field, so equal
/// `Debug` strings mean equal state.
pub fn allocator_is_fresh(allocator: &ExpansionAllocator) -> bool {
    format!("{allocator:?}") == format!("{:?}", ExpansionAllocator::new())
}

pub fn allocator_state(allocator: &ExpansionAllocator) -> String {
    format!("{allocator:?}")
}

pub fn opt_u8(v: Option<u8>) -> Value {
    v.map_or(Value::Null, |x| json!(x))
}

pub fn source_json(source: &SourceInstruction, inline_name: Option<&str>) -> Value {
    let row = source.row();
    let ops = row.operands;
    let inline = match row.inline {
        None => Value::Null,
        Some(key) => json!({
            "opcode": key.opcode,
            "funct3": key.funct3,
            "funct7": key.funct7,
            "name": inline_name.unwrap_or(""),
        }),
    };
    json!({
        "kind": source.kind().name(),
        "address": row.address as u64,
        "rd": opt_u8(ops.rd),
        "rs1": opt_u8(ops.rs1),
        "rs2": opt_u8(ops.rs2),
        "imm": ops.imm.to_string(),
        "inline": inline,
        "is_compressed": row.is_compressed,
    })
}

/// Computes each row's RAF flag the way the witness generator does: build the
/// trace row Jolt would record and run `InstructionRafFlag::extract` on it.
pub struct Annotator {
    preprocessing: JoltProgramPreprocessing,
}

impl Annotator {
    pub fn new() -> Result<Self, String> {
        // A one-row program, as in jolt-witness's test fixture; the RAF
        // extractor reads only the row, but its signature needs an env.
        let addi = JoltInstructionRow {
            instruction_kind: JoltInstructionKind::ADDI,
            address: 0x8000_0000,
            operands: NormalizedOperands {
                rd: Some(1),
                rs1: Some(2),
                rs2: None,
                imm: 3,
            },
            ..Default::default()
        };
        let bytecode = BytecodePreprocessing::preprocess(vec![addi], 0x8000_0000, RV64IMAC_JOLT)
            .map_err(|e| format!("bytecode preprocessing: {e:?}"))?;
        Ok(Self {
            preprocessing: JoltProgramPreprocessing {
                bytecode,
                ram: RAMPreprocessing::default(),
                memory_layout: Default::default(),
                max_padded_trace_length: 4,
            },
        })
    }

    pub fn raf(&self, row: &JoltInstructionRow) -> Result<bool, String> {
        let lowered = JoltInstruction::from(*row);
        let cf = lowered.circuit_flags();
        let is_noop = lowered.instruction_flags().get(InstructionFlags::IsNoop);
        let ram = if cf.get(CircuitFlags::Load) {
            RamAccess::Read(RamRead {
                address: 0,
                value: 0,
            })
        } else if cf.get(CircuitFlags::Store) {
            RamAccess::Write(RamWrite {
                address: 0,
                pre_value: 0,
                post_value: 0,
            })
        } else {
            RamAccess::NoOp
        };
        let pc = u32::from(!is_noop);
        // JoltTraceRow::new rejects a NoOp row that carries sequence or
        // compression metadata (a traced NoOp is padding). Expansion can emit
        // such NoOps (the rd = x0 rewrite of a pure instruction keeps the
        // source metadata), so the trace row for a NoOp drops that metadata.
        // Circuit flags, the only input of the RAF flag, depend on the kind.
        let mut traced = *row;
        if is_noop {
            traced.is_first_in_sequence = false;
            traced.is_compressed = false;
        }
        let trace_row = JoltTraceRow::new(traced, RegisterState::default(), ram, pc)
            .map_err(|e| format!("JoltTraceRow::new for {}: {e:?}", row.instruction_kind.name()))?;
        let env = WitnessEnv::new(&self.preprocessing);
        let flag = InstructionRafFlag::extract(&trace_row, None, &env)
            .map_err(|e| format!("InstructionRafFlag::extract: {e:?}"))?;
        Ok(flag.0)
    }

    pub fn row_json(&self, row: &JoltInstructionRow) -> Result<Value, String> {
        let lowered = JoltInstruction::from(*row);
        let cf = lowered.circuit_flags();
        let inf = lowered.instruction_flags();
        let circuit: Vec<String> = CIRCUIT_FLAGS
            .iter()
            .filter(|f| cf.get(**f))
            .map(|f| format!("{f:?}"))
            .collect();
        let instr: Vec<String> = INSTRUCTION_FLAGS
            .iter()
            .filter(|f| inf.get(**f))
            .map(|f| format!("{f:?}"))
            .collect();
        let table: Option<LookupTableKind<64>> = lowered.lookup_table();
        let table = table.map_or(Value::Null, |t| json!(<&'static str>::from(t)));
        let ops = row.operands;
        Ok(json!({
            "kind": row.instruction_kind.name(),
            "address": row.address as u64,
            "rd": opt_u8(ops.rd),
            "rs1": opt_u8(ops.rs1),
            "rs2": opt_u8(ops.rs2),
            "imm": ops.imm.to_string(),
            "vsr": row.virtual_sequence_remaining.map_or(Value::Null, |v| json!(v)),
            "first": row.is_first_in_sequence,
            "compressed": row.is_compressed,
            "circuit_flags": circuit,
            "instruction_flags": instr,
            "lookup_table": table,
            "raf": self.raf(row)?,
        }))
    }

    pub fn result_json(
        &self,
        result: &Result<Vec<JoltInstructionRow>, ExpansionError>,
    ) -> Result<Value, String> {
        match result {
            Ok(rows) => {
                let rows: Result<Vec<Value>, String> =
                    rows.iter().map(|r| self.row_json(r)).collect();
                Ok(json!({ "rows": rows? }))
            }
            Err(e) => Ok(json!({ "error": format!("{e:?}") })),
        }
    }
}

/// `hex(sha256(serde_json::to_vec(rows)))`, the hash both Jolt fixture tests use.
pub fn rows_sha256(rows: &[JoltInstructionRow]) -> Result<String, String> {
    use sha2::{Digest, Sha256};
    let bytes = serde_json::to_vec(rows).map_err(|e| e.to_string())?;
    Ok(hex::encode(Sha256::digest(bytes)))
}
