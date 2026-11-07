/* (c) Odd mepc, read back, then MRET to it.
 * Sail clears bit 0 (IALIGN = 16); Jolt stores the raw value and MRET jumps to
 * it (JALR clears bit 0 of the target, so control flow still agrees). */
#include "../common.h"
GUEST_START
  la t0, 2f
  ori t0, t0, 1
  csrw mepc, t0
  csrr a0, mepc
  mret
2:
  GUEST_EXIT(0)
GUEST_END
