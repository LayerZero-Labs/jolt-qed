use common::jolt_device::{MemoryConfig, MemoryLayout};
use jolt_claims::protocols::jolt::{JoltPolynomialId, JoltVirtualPolynomial};
use jolt_field::Fr;
use jolt_program::execution::{build_jolt_program, OwnedTrace, TraceInputs};
use jolt_program::preprocess::JoltProgramPreprocessing;
use jolt_prover::ProverConfig;
use jolt_riscv::RV64IMAC_JOLT;
use jolt_witness::backend::JoltWitnessOracle;
use jolt_witness::{JoltVmWitnessConfig, JoltVmWitnessInputs, TraceBackend};
use std::sync::Arc;
use tracer::TracerBackend;

fn main() {
    let elf = std::fs::read(std::env::args().nth(1).expect("ELF path")).unwrap();
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
    println!(
        "lowest={:#x} stack_end={:#x} heap_end={:#x}",
        layout.get_lowest_address(),
        layout.stack_end,
        layout.heap_end
    );

    let program = build_jolt_program(&elf).unwrap();
    let preprocessing = JoltProgramPreprocessing::new(
        program.expanded_bytecode.clone(),
        program.memory_init.clone(),
        layout.clone(),
        program.entry_address,
        256,
        RV64IMAC_JOLT,
    )
    .unwrap();

    // Same steps as jolt-sdk/src/host_utils.rs:313-345.
    let mut backend = TracerBackend::new();
    let compact = backend
        .trace_compact(
            &program,
            TraceInputs::new(vec![], vec![], vec![], memory_config),
            &preprocessing.bytecode,
        )
        .unwrap();
    println!("rows={} panic={}", compact.trace.len(), compact.device.panic);
    for (i, row) in compact.trace.iter().enumerate() {
        if row.is_load() || row.is_store() {
            println!(
                "row={i} store={} load={} ram_address={:#x} slot={:?}",
                row.is_store(),
                row.is_load(),
                row.ram_address(),
                layout.remap_word_address(row.ram_address())
            );
        }
    }

    let config = ProverConfig::derive_compact::<Fr>(
        compact.trace.as_slice(),
        &layout,
        preprocessing.ram.min_bytecode_address,
        preprocessing.ram.bytecode_words.len(),
        256,
    )
    .unwrap();
    println!(
        "min_bytecode_address={:#x} image_words={} trace_length={} ram_K={}",
        preprocessing.ram.min_bytecode_address,
        preprocessing.ram.bytecode_words.len(),
        config.trace_length,
        config.ram_K
    );

    let witness_config = JoltVmWitnessConfig::new(
        config.trace_length.ilog2() as usize,
        config.ram_K,
        config.one_hot_config,
    );
    let program = Arc::new(program);
    let preprocessing = Arc::new(preprocessing);
    let witness = TraceBackend::<OwnedTrace>::from_compact(
        witness_config,
        JoltVmWitnessInputs::new(&program, &preprocessing, compact),
    );
    for (name, id) in [
        ("RamRa", JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamRa)),
        ("RamVal", JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamVal)),
    ] {
        let table: Result<Vec<Fr>, _> = witness.oracle_table(id);
        match table {
            Ok(values) => println!("{name}: ok ({} entries)", values.len()),
            Err(error) => println!("{name}: ERROR {error:?}"),
        }
    }
}
