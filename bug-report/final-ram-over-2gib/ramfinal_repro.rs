use common::jolt_device::{MemoryConfig, MemoryLayout};
use jolt_claims::protocols::jolt::{JoltCommittedPolynomial, JoltPolynomialId, JoltVirtualPolynomial};
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
        heap_size: 0x8000_0000, // 2 GiB heap, so 0x1_0000_0000 is a legal heap address
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
    println!("tracer: rows={} panic={}", compact.trace.len(), compact.device.panic);
    let mut stores = Vec::new();
    for (i, row) in compact.trace.iter().enumerate() {
        if row.is_load() || row.is_store() {
            let slot = layout.remap_word_address(row.ram_address()).unwrap();
            println!(
                "row={i} store={} ram_address={:#x} slot={:?} read={:#x} write={:#x}",
                row.is_store(),
                row.ram_address(),
                slot,
                row.ram_read_value(),
                row.ram_write_value()
            );
            stores.push((i, slot));
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
    println!("prover config: trace_length={} ram_K={}", config.trace_length, config.ram_K);

    let true_slot = layout.remap_word_address(0x1_0000_0000).unwrap().unwrap() as usize;
    let wrong_slot = layout.remap_word_address(0x8000_0000).unwrap().unwrap() as usize;
    // Starting RAM, as Rust's initial RAM: the program image word at RAM_START, zero far above it.
    let init_wrong = preprocessing.ram.bytecode_words[0];
    let init_true = 0u64;

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

    let inc: Vec<Fr> = witness
        .oracle_table(JoltPolynomialId::Committed(JoltCommittedPolynomial::RamInc))
        .unwrap();
    let changes = |slot: usize| -> Fr {
        stores
            .iter()
            .filter(|(_, s)| *s == Some(slot as u64))
            .map(|(i, _)| inc[*i])
            .fold(Fr::from(0u64), |a, b| a + b)
    };
    let (changes_wrong, changes_true) = (changes(wrong_slot), changes(true_slot));

    println!("building RamValFinal ({} slots)...", config.ram_K);
    let final_val: Vec<Fr> = witness
        .oracle_table(JoltPolynomialId::Virtual(JoltVirtualPolynomial::RamValFinal))
        .unwrap();
    for (name, slot, init, changes) in [
        ("RAM_START (0x80000000)", wrong_slot, init_wrong, changes_wrong),
        ("0x1_0000_0000", true_slot, init_true, changes_true),
    ] {
        let expected = Fr::from(init) + changes;
        println!(
            "slot {slot} at {name}: RamValFinal={:?} | RamValInit + sum(RamInc*ra)={:?} | check holds={}",
            final_val[slot],
            expected,
            final_val[slot] == expected
        );
    }
}
