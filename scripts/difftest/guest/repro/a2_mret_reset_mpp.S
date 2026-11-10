/* (a, variant) MRET with mstatus as left by reset (no MPP write).
 * With U-mode enabled, Sail resets MPP to U, so MRET drops to U-mode and the
 * following CSR read traps as an illegal instruction. Jolt has only M-mode.
 * On an M-only configuration MPP reads as M and both stay in M-mode. */
  .section .text.init
  .globl _start
_start:
  li a0, 0
  li a1, 0
  la t0, trap_handler
  csrw mtvec, t0
  la t0, 2f
  csrw mepc, t0
  mret
2:
  csrr a0, mstatus
  li t6, 1
  la t5, tohost
  sd t6, 0(t5)
1: j 1b
  .align 2
trap_handler:
  csrr s2, mcause
  csrr s3, mepc
  csrr s4, mtval
  li t6, 1
  la t5, tohost
  sd t6, 0(t5)
1: j 1b
  .section .tohost, "aw", @progbits
  .align 6
  .globl tohost
tohost: .dword 0
  .globl fromhost
fromhost: .dword 0
