/* (g) EBREAK. Spec (Sail): breakpoint trap (mcause 3, mtval = pc).
 * Jolt main (9407f93fb): EBREAK is a self-jump, which the tracer treats as
 * halt. */
#include "../common.h"
GUEST_START
  ebreak
  GUEST_EXIT(1)
GUEST_END
