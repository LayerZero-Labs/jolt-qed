/* (d, related) LR.W at scratch, SC.W at scratch + 4 (same 8-byte granule). */
#include "../common.h"
GUEST_START
  la a2, scratch
  lr.w t1, (a2)
  li t2, 0x55
  addi a4, a2, 4
  sc.w t3, t2, (a4)
  ld a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
