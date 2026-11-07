/* (e) LR.W at an address that is 2 mod 4.
 * Spec (Sail): load address misaligned (mcause 4), mtval = address. */
#include "../common.h"
GUEST_START
  la a2, scratch
  addi a2, a2, 2
  lr.w t1, (a2)
  GUEST_EXIT(1)
GUEST_END
