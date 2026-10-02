+++
title = "Setup: Jolt As A Black Box"
date = 2026-10-01
draft = true
+++

Jolt is a state-of-the-art zero-knowledge virtual machine (zk-VM) that is intended to power the proving machinery of blockchains. 
A traditional virtual machine executes a guest program compiled for a specified instruction set architecture (ISA), such as RISC-V, ARM, x86, etc. by emulating the guest CPU in software. 
A zk-VM is a virtual machine with the added responsibility that it is required to output an efficiently checkable cryptographic proof that it executed every instruction of the guest program correctly.

TODO: (ari) Put in a picture. 

Ok so our first task is to get a guest program

## Find valid RISC-V program

We went ahead and found a [guest program](https://github.com/abiswas3/jolt-tutorial/blob/failing-elf/program/disassembly.txt) ([download the ELF](program.elf))
Instructions on how to create this elf can be found [here](https://github.com/abiswas3/jolt-tutorial/blob/failing-elf/program/README.md)

Now lets try to prove this.
We will dive deep into what each line means in a bit, but for now the following code allows us to read in the elf file, prepare it, ask Jolt to prove one run of it, and check the proof.
The program takes two arguments, `x` and `y`, and we want to give it the inputs 2 and 3.
So the first byte array passed to `prove_program`, `&[2, 3]`, is the input bytes.
The other empty arguments to `prove_program` are for advice, extra data a program can be given, which we come to later.

```rust
// Ask Jolt to prove one run of a RISC-V executable, then check the proof.
use std::path::PathBuf;

fn main() {
    let elf_path = std::env::args()
        .nth(1)
        .expect("usage: prover <path to RISC-V ELF>");

    // The program to prove: just the ELF file. Nothing is compiled here.
    let mut program = jolt_sdk::host::Program::new("program");
    program.elf = Some(PathBuf::from(elf_path));

    // Prepare the data the prover and the verifier need about the program.
    let preprocessing = jolt_sdk::preprocess_program(
        &mut program,
        jolt_sdk::MemoryConfig::default(),
        1 << 16, // longest run allowed, in instructions
        None,
    )
    .expect("preprocessing failed");

    // Prove one run, with the input bytes [2, 3] and no advice.
    let (proof, io_device) =
        jolt_sdk::prove_program(&program, &preprocessing, &[2, 3], &[], &[], None, None, None)
            .expect("proving failed");
// ,,,
    ```

To run the prover, we build it, then give it the path of the ELF file:

```text
cd jolt-tutorial-run/prover
cargo build --release
./target/release/prover \
  ../program/target/riscv64imac-unknown-none-elf/release/program
```

The first build takes a few minutes, because it compiles all of Jolt.
The prover fails with:

```text
thread 'main' panicked at src/main.rs:20:6:
preprocessing failed: InvalidProgram { reason: "entry address is absent from bytecode preprocessing" }
```

Ok, well that does not work. 
Let's debug

## Getting A Working Trace

### All the checks

### Check 1: ELF file

The file must be one that `object`, the library Jolt uses to read executables, can parse as an ELF file.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/image/elf.rs#L33-L34)

```text
parse the file as ELF          else stop: "invalid ELF object"
```

### Check 2: 64-bit

Jolt only accepts 64-bit ELF files.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/image/elf.rs#L35-L39)

```text
if the ELF file is 32-bit:     stop: "supports RV64/ELF64 program images only"
```

### Check 3: code decodes

Every byte of every code section must belong to a RISC-V instruction Jolt recognises, read one after another from the start of the section.
So a code section cannot contain data, and its last instruction cannot be cut off.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/image/elf.rs#L107-L146)

```text
for each code section, from its first byte to its last:
    two zero bytes:                     skip them (padding)
    lowest two bits not 11:             a 2-byte instruction
    lowest two bits 11:                 a 4-byte instruction
    instruction cut off by the end:     stop: "truncated ..."
    instruction not recognised:         stop: "unknown RV64 opcode", or similar
```

### Check 4: supported instructions

Every instruction must be one that Jolt supports.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/image/decode.rs#L70-L72)

```text
for each instruction:
    if Jolt does not support it:   stop: IllegalSourceInstruction
```

### Check 5: expansion

Jolt rewrites every RISC-V instruction into one or more instructions of its own instruction set.
This rewriting must succeed.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/expand/mod.rs#L291-L307)

```text
for each instruction:
    rewrite it into one or more of Jolt's own instructions    else stop: ExpansionError
```

### Check 6: allowed Jolt instructions

After the rewriting, every instruction must be one Jolt allows.
No instruction may both store to memory and write a register.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/preprocess/bytecode.rs#L39-L46)

```text
for each Jolt instruction:
    if Jolt does not allow it:                stop: IllegalTargetInstruction
    if it stores to memory and names rd:      stop: StoreWritesRd
```

### Check 7: instruction addresses

Every instruction address must be even, and at or above `0x80000000`.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/preprocess/bytecode.rs#L247-L254)

```text
for each instruction address a:
    if a < 0x80000000 or a is odd:   stop: InvalidBytecodeAddress
```

### Check 8: entry address

The ELF's entry address, where the program starts, must be the address of one of its instructions.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-prover/src/preprocessing.rs#L34-L41)

```text
if no instruction is at the ELF's entry address:
    stop: "entry address is absent from bytecode preprocessing"
```

### Check 9: input size

The input and the two kinds of advice must each fit within their maximum size.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/lib.rs#L382-L399)

```text
if the trusted advice is longer than its maximum size:     stop
if the untrusted advice is longer than its maximum size:   stop
if the input is longer than its maximum size:              stop
```

### Check 10: memory accesses

Every load and store must go to an allowed address.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/emulator/mmu.rs#L144-L220)

```text
if address < 0x80000000:
    if address > 0x7FFFC010:                                stop: "I/O overflow"
    if store, and not to output, panic or termination:     stop: "Illegal device store"
else:
    if address >= heap_end:                                 stop
    if store, into the stack canary:                        stop: "Stack overflow"
```

### Check 11: stopping

The run ends when the program jumps to itself, or when an instruction cannot run.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/lib.rs#L329-L339)

```text
loop:
    if pc is the same as before the last step:   stop the run   (the program jumps to itself)
    run one instruction
    if it recorded nothing (a trap):            stop the run
```

### Check 12: executed instructions

Every instruction the program runs must be one Jolt found in the ELF file.
What it reads and writes must follow the rules for its kind of instruction.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/trace_row.rs#L129-L148)

```text
for each instruction the run executed:
    if it is not in Jolt's instruction list from the ELF:          stop: MissingBytecodePc
    if its recorded values break the rules for its kind:          stop: MemoryRowContractViolation
```

### Check 13: trace length

The run must not be too long for the maximum trace length given to preprocessing.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-prover/src/config.rs#L114-L123)

```text
length = 256                                  if fewer than 256 instructions ran
         (instructions run + 1), rounded up to a power of two    otherwise
if length > the maximum trace length:   stop: "trace exceeds the preprocessing's maximum padded trace length"
```

### Check 14: termination word

A program that did not panic must store `1` at the termination word before it stops.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/preprocess/public_io.rs#L21-L52)

```text
if the program did not panic:
    the word at 0x7FFFC008 must be 1 at the end of the run
```

### Check 15: public I/O memory

At the end of the run, the I/O region of memory must hold the inputs, the outputs the verifier is told, the panic word and the termination word, and zeros everywhere else.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L120-L128)

```text
at the end of the run, memory from 0x7FFFA000 up to 0x80000000 must hold:
    the input bytes, the output bytes the verifier is told,
    the panic word, the termination word (check 14), and 0 everywhere else
```

### The initial state

### Initial memory

Jolt only uses the sections whose address is at or above `0x80000000`.
Any other section is ignored, without an error.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/image/elf.rs#L46-L74)

```text
for each section:
    if its address < 0x80000000:   skip it, with no error
    else:                          its bytes become initial memory
                                   if it is code, its bytes are decoded (check 3)
```

### Initial registers

When the program starts, every register is 0, including the stack pointer.
The program counter is the ELF's entry address.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/emulator/cpu.rs#L521)

```text
every register = 0, including the stack pointer
pc             = the ELF's entry address
```

### Inputs in memory

The program gets its input from memory, not from registers.
Jolt puts the input bytes in the input region, which starts at `0x7FFFA000` for the default sizes.

[code](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L439-L449)

The inputs are not in registers.
They are in memory, in the input region.
This is the memory map for the default sizes:

```text
 address                     region
 --------------------------  ------------------------------------------------
 heap_end                    -----------------------------------------------
                             heap
                             stack
                             stack canary, 128 bytes
 0x80000000 + program size   -----------------------------------------------
                             the program: its code and data
 0x80000000                  ======== RAM_START_ADDRESS ========
                             no access
 0x7FFFC010                  -----------------------------------------------
 0x7FFFC008                  termination word
 0x7FFFC000                  panic word
 0x7FFFB000                  output
 0x7FFFA000                  input
 0x7FFF9000                  untrusted advice
 0x7FFF8000                  trusted advice
                             loads read 0, stores not allowed
 0x00000000                  -----------------------------------------------
```

```text
load byte at 0x7FFFA000 + i   =   input byte i, or 0 past the end of the input
```

## Making Jolt accept our ELF file

Now here is what we needed to change to make Jolt accept our elf file.

1. A new file, `jolt-tutorial-run/program/link.ld`.
   It is a linker script, the file that tells the linker where each part of the program goes in memory.
   It puts the code at `0x80000000`:

   ```text,name=jolt-tutorial-run/program/link.ld
   /* Start running at _start. */
   ENTRY(_start)

   SECTIONS
   {
     /* Jolt only reads code at or above 0x80000000, so put the code there. */
     . = 0x80000000;
     .text : { *(.text .text.*) }
   }
   ```

   `ENTRY(_start)` makes the address of `_start` the ELF's entry address.
   `. = 0x80000000;` sets the current address, and `.text : { ... }` puts all the code there.

2. A new file, `jolt-tutorial-run/program/.cargo/config.toml`.
   It makes the linker use `link.ld`, by passing it the flag `-Tlink.ld`.
   Cargo reads `.cargo/config.toml` from the folder you run it in and the folders above it, so it uses this file whenever we build inside `program/`:

   ```toml,name=jolt-tutorial-run/program/.cargo/config.toml
   [target.riscv64imac-unknown-none-elf]
   # Link with our linker script, link.ld, in this folder.
   rustflags = ["-C", "link-arg=-Tlink.ld"]
   ```

3. Changes to `jolt-tutorial-run/program/src/main.rs`:
   - `_start` takes no arguments, and reads the inputs from memory, at `0x7FFFA000`.
   - It writes the output to memory, at `0x7FFFB000`.
   - It stores `1` at the termination word, `0x7FFFC008`, before jumping to itself.
   - It no longer uses `black_box`, so it no longer uses the stack, whose pointer starts at 0.

   ```rust,name=jolt-tutorial-run/program/src/main.rs
   #![no_std]
   #![no_main]

   // Jolt's input, output and termination addresses, for the default memory sizes.
   const INPUT: usize = 0x7FFF_A000;
   const OUTPUT: usize = 0x7FFF_B000;
   const TERMINATION: usize = 0x7FFF_C008;

   #[no_mangle]
   pub extern "C" fn _start() -> ! {
       unsafe {
           let x = core::ptr::read_volatile(INPUT as *const u8) as u32;
           let y = core::ptr::read_volatile((INPUT + 1) as *const u8) as u32;
           core::ptr::write_volatile(OUTPUT as *mut u32, x + y);
           core::ptr::write_volatile(TERMINATION as *mut u8, 1);
       }
       loop {}
   }

   #[panic_handler]
   fn panic(_: &core::panic::PanicInfo) -> ! {
       loop {}
   }
   ```

To build it and prove it:

```text
cd jolt-tutorial-run/program
cargo build --release --target riscv64imac-unknown-none-elf
cd ../prover
./target/release/prover \
  ../program/target/riscv64imac-unknown-none-elf/release/program
```

It prints:

```text
verify: Ok(())
```

## Jolt state

Jolt's state has four parts:

- the registers: 32 RISC-V registers and 96 virtual registers;
- the program counter;
- the memory (RAM);
- the device: the inputs, outputs, advice, panic word and termination word.

The memory and the device are built differently, but logically they form one big table, from addresses to bytes.
The table is divided into regions.
Each region belongs to one part of the state, and has its own rules for reading and writing.
For the default sizes:

| Region | Addresses | Read | Write |
|---|---|---|---|
| zero padding | `0x00000000` – `0x7FFF7FFF` | reads 0 | no |
| trusted advice | `0x7FFF8000` – `0x7FFF8FFF` | yes | no |
| untrusted advice | `0x7FFF9000` – `0x7FFF9FFF` | yes | no |
| input | `0x7FFFA000` – `0x7FFFAFFF` | yes | no |
| output | `0x7FFFB000` – `0x7FFFBFFF` | yes | yes |
| panic word | `0x7FFFC000` – `0x7FFFC007` | the panic flag | sets the panic flag |
| termination word | `0x7FFFC008` – `0x7FFFC00F` | reads 0 | ignored |
| gap | `0x7FFFC010` – `0x7FFFFFFF` | no | no |
| program, stack canary, stack, heap | `0x80000000` – end of heap | yes | yes, except the stack canary |

Everything below `0x80000000` is the device.
Everything from `0x80000000` up is the memory.
The proof does not tell them apart: it treats the table, from the trusted advice upwards, as one array of 8-byte words.
