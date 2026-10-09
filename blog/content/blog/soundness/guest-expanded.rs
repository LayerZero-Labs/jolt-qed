// guest/src/lib.rs after macro expansion (cargo rustc -Zunpretty=expanded, guest feature, riscv64imac-unknown-none-elf)
#![feature(prelude_import)]
#![no_std]
extern crate core;
#[prelude_import]
use core::prelude::rust_2021::*;

pub fn add(x: u32, y: u32) -> u32 { { x + y } }
#[no_mangle]
pub extern "C" fn main() -> ! {
    let mut offset = 0;
    let input_ptr = 2147459072u64 as *const u8;
    let input_slice =
        unsafe { core::slice::from_raw_parts(input_ptr, 4096usize) };
    let untrusted_advice_ptr = 2147454976u64 as *const u8;
    let untrusted_advice_slice =
        unsafe {
            core::slice::from_raw_parts(untrusted_advice_ptr, 4096usize)
        };
    let trusted_advice_ptr = 2147450880u64 as *const u8;
    let trusted_advice_slice =
        unsafe { core::slice::from_raw_parts(trusted_advice_ptr, 4096usize) };
    let (x, input_slice) =
        jolt::postcard::take_from_bytes::<u32>(input_slice).unwrap();
    ;
    let (y, input_slice) =
        jolt::postcard::take_from_bytes::<u32>(input_slice).unwrap();
    ;
    fn __jolt_guest_add(x: u32, y: u32) -> u32 { x + y }
    let to_return = __jolt_guest_add(x, y);
    let output_ptr = 2147463168u64 as *mut u8;
    let output_slice =
        unsafe { core::slice::from_raw_parts_mut(output_ptr, 4096usize) };
    jolt::postcard::to_slice::<u32>(&to_return, output_slice).unwrap();
    unsafe { core::ptr::write_volatile(2147467272usize as *mut u8, 1); }
    loop { unsafe { asm!("j .", options(noreturn)); } }
}
#[no_mangle]
pub extern "C" fn jolt_panic() {
    unsafe { core::ptr::write_volatile(2147467264u64 as *mut u8, 1); }
}

// guest/src/main.rs after macro expansion
#![feature(prelude_import)]
#![no_std]
#![no_main]
extern crate core;
#[prelude_import]
use core::prelude::rust_2021::*;

#[allow(unused_imports)]
use add_guest::*;
