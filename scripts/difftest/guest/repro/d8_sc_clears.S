/* (d, related) Every SC clears the reservation: a successful SC.W followed
 * by a second SC.W, and a failing SC.W (other address) followed by an SC.W
 * at the reserved address. Both second SCs fail. */
#include "../common.h"
GUEST_START
  la a2, scratch
  li t2, 0x55
  lr.w t1, (a2)
  sc.w t3, t2, (a2)
  sc.w t4, t2, (a2)
  addi a4, a2, 16
  lr.w t1, (a2)
  sc.w t5, t2, (a4)
  sc.w s6, t2, (a2)
  ld a3, 0(a2)
  ld a5, 16(a2)
  GUEST_EXIT(0)
GUEST_END
