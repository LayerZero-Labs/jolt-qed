/* (d, related) LR.W, then ECALL into a handler that returns with MRET, then
 * SC.W at the same address. Shows whether a trap and its return clear the
 * reservation. */
#include "../common.h"
GUEST_START
  la t0, 2f
  csrw mtvec, t0
  la a2, scratch
  lr.w t1, (a2)
  ecall
  li t2, 0x55
  sc.w t3, t2, (a2)
  ld a3, 0(a2)
  GUEST_EXIT(0)
  .align 2
2:
  csrr t0, mepc
  addi t0, t0, 4
  csrw mepc, t0
  mret
GUEST_END
