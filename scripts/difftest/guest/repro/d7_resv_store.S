/* (d, related) LR.W, then a plain store by the same hart to the reserved
 * word, then SC.W there. A same-hart store need not clear the reservation. */
#include "../common.h"
GUEST_START
  la a2, scratch
  lr.w t1, (a2)
  li t4, 0x77
  sw t4, 0(a2)
  li t2, 0x55
  sc.w t3, t2, (a2)
  ld a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
