/* (d) SC.W with no reservation.
 * Spec (Sail): fails, rd = 1, no memory write.
 * Jolt main (9407f93fb): rd = 1 and a store of the old value. */
#include "../common.h"
GUEST_START
  la a2, scratch
  li t2, 0x55
  sc.w t1, t2, (a2)
  lw a3, 0(a2)
  GUEST_EXIT(0)
GUEST_END
