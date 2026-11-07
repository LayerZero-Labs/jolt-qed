//! Run an ELF through Jolt's tracer in trace mode (each instruction executes
//! its inline sequence, as the Jolt prover sees it) and print one JSON line per
//! retired RISC-V instruction.
//!
//! Each line records what that instruction changed:
//!   pc    address of the instruction
//!   next  pc after it
//!   x     integer registers written, as {"index": value}
//!   csr   machine CSRs Jolt keeps in virtual registers 34..39, when changed
//!   resv  LR/SC reservation registers 32 (word) and 33 (doubleword), when changed
//!   mem   RAM writes as [address, pre, post] (doubleword granularity)
//! The last line is {"end": ...}: "tohost" with the HTIF payload, "halt" for
//! a self-loop (Jolt's termination), "limit", or "panic" with the message.
//!
//! Usage: jolt-trace ELF [--limit N]

use std::panic::{catch_unwind, AssertUnwindSafe};

use common::jolt_device::{JoltDevice, MemoryConfig};
use jolt_riscv::trace_row::RamAccess;
use tracer::emulator::{default_terminal::DefaultTerminal, Emulator};
use tracer::instruction::Cycle;

const CSRS: [(usize, &str); 6] = [
    (34, "mtvec"),
    (35, "mscratch"),
    (36, "mepc"),
    (37, "mcause"),
    (38, "mtval"),
    (39, "mstatus"),
];

fn hex(v: u64) -> String {
    format!("\"0x{v:016x}\"")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let elf = args.get(1).expect("usage: jolt-trace ELF [--limit N]");
    let limit: u64 = match args.get(2).map(String::as_str) {
        Some("--limit") => args[3].parse().expect("--limit takes a number"),
        _ => 100_000,
    };

    // Silence the tracer's own panic message; the panic is reported as JSON.
    std::panic::set_hook(Box::new(|_| {}));

    let elf_content = std::fs::read(elf).expect("cannot read ELF");
    let mut emu = Emulator::new(Box::new(DefaultTerminal::default()));
    emu.setup_program(&elf_content);
    // Same device setup as the jolt-emu binary.
    let memory_config = MemoryConfig {
        program_size: Some(elf_content.len() as u64),
        ..Default::default()
    };
    emu.get_mut_cpu().get_mut_mmu().jolt_device = Some(JoltDevice::new(&memory_config));
    let tohost = emu.tohost_addr;

    for step in 0..limit {
        if emu.get_cpu().has_stalled() {
            println!("{{\"end\":\"halt\",\"pc\":{}}}", hex(emu.get_cpu().read_pc()));
            return;
        }
        let pc = emu.get_cpu().read_pc();
        let before = emu.get_cpu().x;
        let mut rows: Vec<Cycle> = Vec::new();
        let result = catch_unwind(AssertUnwindSafe(|| emu.tick(Some(&mut rows))));
        if let Err(payload) = result {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            println!(
                "{{\"end\":\"panic\",\"step\":{step},\"pc\":{},\"msg\":{}}}",
                hex(pc),
                serde_json::to_string(&msg).unwrap()
            );
            return;
        }
        let cpu = emu.get_cpu();
        let after = cpu.x;
        let mut fields = vec![format!("\"step\":{step}"), format!("\"pc\":{}", hex(pc))];
        fields.push(format!("\"next\":{}", hex(cpu.read_pc())));
        let x: Vec<String> = (1..32)
            .filter(|&i| before[i] != after[i])
            .map(|i| format!("\"{i}\":{}", hex(after[i] as u64)))
            .collect();
        fields.push(format!("\"x\":{{{}}}", x.join(",")));
        let csr: Vec<String> = CSRS
            .iter()
            .filter(|(i, _)| before[*i] != after[*i])
            .map(|(i, n)| format!("\"{n}\":{}", hex(after[*i] as u64)))
            .collect();
        fields.push(format!("\"csr\":{{{}}}", csr.join(",")));
        let resv: Vec<String> = [32usize, 33]
            .iter()
            .filter(|&&i| before[i] != after[i])
            .map(|&i| format!("\"{i}\":{}", hex(after[i] as u64)))
            .collect();
        fields.push(format!("\"resv\":{{{}}}", resv.join(",")));
        let mem: Vec<String> = rows
            .iter()
            .filter_map(|row| match row.ram_access() {
                RamAccess::Write(w) => Some(format!(
                    "[{},{},{}]",
                    hex(w.address),
                    hex(w.pre_value),
                    hex(w.post_value)
                )),
                _ => None,
            })
            .collect();
        fields.push(format!("\"mem\":[{}]", mem.join(",")));
        println!("{{{}}}", fields.join(","));

        if tohost != 0 {
            let value = emu.get_mut_cpu().get_mut_mmu().load_doubleword_raw(tohost);
            if value != 0 {
                println!("{{\"end\":\"tohost\",\"value\":{}}}", hex(value));
                return;
            }
        }
    }
    println!("{{\"end\":\"limit\"}}");
}
