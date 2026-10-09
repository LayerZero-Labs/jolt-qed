// Prove the SC.W test ELF with Jolt's prover and check the proof with Jolt's
// verifier. Run with JOLT_CHEAT_SC_FAIL=1 to make the (patched) tracer report
// SC.W failure even when the reservation holds.
use jolt_sdk::host::JoltProgramSource;
use jolt_sdk::MemoryConfig;

struct RawElf(Vec<u8>);

impl JoltProgramSource for RawElf {
    fn get_elf_contents(&self) -> Option<Vec<u8>> {
        Some(self.0.clone())
    }
    fn get_elf_compute_advice_contents(&self) -> Option<Vec<u8>> {
        None
    }
}

fn main() {
    let elf = std::fs::read(std::env::args().nth(1).expect("ELF path")).unwrap();
    let mut source = RawElf(elf);
    let memory_config = MemoryConfig {
        max_input_size: 0,
        max_trusted_advice_size: 0,
        max_untrusted_advice_size: 0,
        max_output_size: 8,
        stack_size: 4096,
        heap_size: 4096,
        program_size: None,
    };
    let prover_preprocessing =
        jolt_sdk::preprocess_program(&mut source, memory_config, 1 << 10, None).unwrap();
    let verifier_preprocessing = jolt_sdk::verifier_preprocessing_from_prover(&prover_preprocessing);

    let cheat = std::env::var_os("JOLT_CHEAT_SC_FAIL").is_some();
    let (proof, device) =
        jolt_sdk::prove_program(&source, &prover_preprocessing, &[], &[], &[], None, None, None)
            .unwrap();
    println!(
        "cheat={cheat} output_start={:#x} outputs={:?} panic={}",
        device.memory_layout.output_start, device.outputs, device.panic
    );

    let result = jolt_sdk::jolt_verifier::verify::<
        jolt_sdk::VerifierField,
        jolt_sdk::VerifierPCS,
        jolt_sdk::VerifierVC,
        jolt_sdk::VerifierTranscript,
    >(&verifier_preprocessing, &device, &proof, None);
    println!("verifier: {result:?}");
}
