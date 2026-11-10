/* (e, related) SC.W at an address that is 2 mod 4 with no reservation.
 * Spec (Sail): store/AMO address misaligned (mcause 6). */
#include "../common.h"
GUEST_START
  la a2, scratch
  addi a2, a2, 2
  li t2, 0x55
  sc.w t1, t2, (a2)
  GUEST_EXIT(1)
GUEST_END
