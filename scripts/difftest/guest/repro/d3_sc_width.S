/* (d, related) LR.W then SC.D at the same address. */
#include "../common.h"
GUEST_START
  la a2, scratch
  lr.w t1, (a2)
  li t2, 0x55
  sc.d t3, t2, (a2)
  ld a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
