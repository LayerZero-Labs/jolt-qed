use common::jolt_device::{MemoryConfig, MemoryLayout};
use jolt_program::execution::{build_jolt_program, ExecutionBackend, TraceInputs};
use jolt_program::preprocess::JoltProgramPreprocessing;
use jolt_riscv::RV64IMAC_JOLT;
use jolt_claims::protocols::jolt::{JoltCommittedPolynomial, JoltPolynomialId, JoltVirtualPolynomial};
use jolt_field::Fr;
use jolt_program::execution::OwnedTrace;
use jolt_witness::backend::JoltWitnessOracle;
use jolt_witness::{JoltVmWitnessConfig, JoltVmWitnessInputs, TraceBackend};
use std::sync::Arc;
use tracer::TracerBackend;

fn main() {
    let elf_path = std::env::args().nth(1).expect("expected guest ELF path");
    let elf = std::fs::read(elf_path).unwrap();
    let memory_config = MemoryConfig {
        max_input_size: 0,
        max_trusted_advice_size: 0,
        max_untrusted_advice_size: 0,
        max_output_size: 8,
        stack_size: 4096,
        heap_size: 4096,
        program_size: Some(elf.len() as u64),
    };
    let layout = MemoryLayout::new(&memory_config);
    println!("termination={:#x}", layout.termination);
    let program = build_jolt_program(&elf).unwrap();
    println!("bytecode_rows={}", program.expanded_bytecode.len());
    println!("final_jal_rd={:?}", program.expanded_bytecode[5].operands.rd);
    let mut backend = TracerBackend::new();
    let output = backend.trace(&program, TraceInputs::new(vec![], vec![], vec![], memory_config)).unwrap();
    let rows = output.trace.rows();
    println!("rows={} panic={}", rows.len(), output.device.panic);
    for (i, row) in rows.iter().enumerate() {
        println!("row={i} kind={:?} ram={:?}", row.instruction_kind(), row.ram_access());
    }
    let preprocessing = JoltProgramPreprocessing::new(
        program.expanded_bytecode.clone(), program.memory_init.clone(),
        layout.clone(), program.entry_address, 256, RV64IMAC_JOLT,
    ).unwrap();
    let compact = backend.trace_compact(
        &program,
        TraceInputs::new(vec![], vec![], vec![], memory_config),
        &preprocessing.bytecode,
    ).unwrap();
    println!("compact_rows={} compact_panic={}", compact.trace.len(), compact.device.panic);
    for (i, row) in compact.trace.iter().enumerate() {
        if row.is_load() || row.is_store() {
            println!("compact_row={i} store={} load={} ram_address={:#x} ram_read={:#x} ram_write={:#x}",
                row.is_store(), row.is_load(), row.ram_address(), row.ram_read_value(), row.ram_write_value());
        }
    }
    let address = layout.remap_word_address(layout.termination).unwrap().unwrap() as usize;
    let mut config = JoltVmWitnessConfig::default();
    config.log_t = 8;
    config.ram_k = 16;
    let program = Arc::new(program);
    let preprocessing = Arc::new(preprocessing);
    let witness = TraceBackend::<OwnedTrace>::from_compact(
        config, JoltVmWitnessInputs::new(&program, &preprocessing, compact),
    );
    let val: Vec<Fr> = witness.oracle_table(JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamVal)).unwrap();
    let final_val: Vec<Fr> = witness.oracle_table(JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamValFinal)).unwrap();
    let ra: Vec<Fr> = witness.oracle_table(JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamRa)).unwrap();
    let inc: Vec<Fr> = witness.oracle_table(JoltPolynomialId::Committed(JoltCommittedPolynomial::RamInc)).unwrap();
    let mut prefix = Fr::from(0u64);
    for cycle in 0..4 {
        prefix += ra[address * 256 + cycle] * inc[cycle];
    }
    let initial = val[address * 256];
    let current = val[address * 256 + 4];
    println!("word_index={address} init={initial:?} prefix={prefix:?} ram_val_t4={current:?} eq={}", current == initial + prefix);
    println!("ra_t3={:?} inc_t3={:?} ra_t4={:?}", ra[address * 256 + 3], inc[3], ra[address * 256 + 4]);
    let gamma = Fr::from(7u64);
    let lhs = current + gamma * final_val[address] - (Fr::from(1u64) + gamma) * initial;
    let rhs = (Fr::from(1u64) + gamma) * prefix;
    println!("final={:?} gamma7_lhs={lhs:?} gamma7_rhs={rhs:?} gamma7_eq={}", final_val[address], lhs == rhs);
}
