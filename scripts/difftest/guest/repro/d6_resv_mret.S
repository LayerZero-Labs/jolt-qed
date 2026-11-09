/* (d, related) LR.W, then an MRET to the next instruction (no trap), then
 * SC.W at the same address. Shows whether MRET clears the reservation. */
#include "../common.h"
GUEST_START
  la a2, scratch
  lr.w t1, (a2)
  la t0, 2f
  csrw mepc, t0
  mret
2:
  li t2, 0x55
  sc.w t3, t2, (a2)
  ld a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
