/* (f) Set mstatus.FS = 3 and read it back. */
#include "../common.h"
GUEST_START
  li t0, 0x6000
  csrs mstatus, t0
  csrr a0, mstatus
  GUEST_EXIT(0)
GUEST_END
