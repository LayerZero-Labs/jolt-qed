/* (c) Write all ones to mstatus and read it back.
 * Sail legalizes (WARL); Jolt main (9407f93fb) stores the raw value. */
#include "../common.h"
GUEST_START
  li t0, -1
  csrw mstatus, t0
  csrr a0, mstatus
  li t0, 0
  csrw mstatus, t0
  csrr a1, mstatus
  GUEST_EXIT(0)
GUEST_END
