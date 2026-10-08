use common::constants::RAM_START_ADDRESS;
use common::jolt_device::{MemoryConfig, MemoryLayout};
use jolt_crypto::{Bn254G1, Pedersen};
use jolt_dory::DoryScheme;
use jolt_field::Fr;
use jolt_program::execution::{build_jolt_program, TraceInputs};
use jolt_program::preprocess::{compute_min_ram_k, compute_max_ram_k, JoltProgramPreprocessing};
use jolt_prover::ProverConfig;
use jolt_riscv::RV64IMAC_JOLT;
use jolt_verifier::{JoltVerifierPreprocessing, ProgramPreprocessing, validate_inputs_from_parts};
use std::sync::Arc;
use tracer::TracerBackend;

fn main() {
    let elf = std::fs::read(std::env::args().nth(1).expect("ELF path")).unwrap();
    let program = build_jolt_program(&elf).unwrap();
    let memory_config = MemoryConfig {
        max_input_size: 0,
        max_trusted_advice_size: 0,
        max_untrusted_advice_size: 0,
        max_output_size: 64,
        stack_size: 0,
        heap_size: 0,
        program_size: Some(program.program_end - RAM_START_ADDRESS),
    };
    let layout = MemoryLayout::new(&memory_config);
    let preprocessing = JoltProgramPreprocessing::new(
        program.expanded_bytecode.clone(), program.memory_init.clone(),
        layout.clone(), program.entry_address, 256, RV64IMAC_JOLT,
    ).unwrap();
    assert!(preprocessing.metadata().is_some());
    let mut backend = TracerBackend::new();
    let compact = backend.trace_compact(
        &program, TraceInputs::new(vec![], vec![], vec![], memory_config),
        &preprocessing.bytecode,
    ).unwrap();
    let config = ProverConfig::derive_compact::<Fr>(
        compact.trace.as_slice(), &layout, preprocessing.ram.min_bytecode_address,
        preprocessing.ram.bytecode_words.len(), 256,
    ).unwrap();
    let minimum = compute_min_ram_k(preprocessing.ram.min_bytecode_address,
        preprocessing.ram.bytecode_words.len(), &layout).unwrap();
    let maximum = compute_max_ram_k(&layout).unwrap();
    println!("entry={:#x} image_bytes={} image_words={} trace_rows={}",
        program.entry_address, program.memory_init.len(), preprocessing.ram.bytecode_words.len(),
        compact.trace.len());
    println!("trace_length={} ram_K={} verifier_min={} verifier_max={}",
        config.trace_length, config.ram_K, minimum, maximum);
    let verifier = JoltVerifierPreprocessing::<DoryScheme, Pedersen<Bn254G1>>::new(
        ProgramPreprocessing::Full(Arc::new(preprocessing)),
        DoryScheme::setup_verifier(4), None,
    ).unwrap();
    let result = validate_inputs_from_parts(&verifier, &compact.device,
        config.trace_length, config.ram_K, config.trace_polynomial_order, config.one_hot_config,
        false, false, false);
    match result {
        Ok(_) => println!("verifier input checks: accepted"),
        Err(error) => println!("verifier input checks: {error:?}"),
    }
}
