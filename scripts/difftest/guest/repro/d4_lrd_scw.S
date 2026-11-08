/* (d, related) LR.D then SC.W at the same address: the SC is narrower than
 * the LR, so it succeeds under the reservation rule "same address, SC no
 * wider than LR". */
#include "../common.h"
GUEST_START
  la a2, scratch
  lr.d t1, (a2)
  li t2, 0x55
  sc.w t3, t2, (a2)
  ld a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
