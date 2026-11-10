/* (c) mtvec with reserved MODE values 2 and 3, and with MODE = 1 (vectored).
 * Each write is read back. */
#include "../common.h"
GUEST_START
  la t1, trap_handler
  ori t0, t1, 2
  csrw mtvec, t0
  csrr a0, mtvec
  ori t0, t1, 3
  csrw mtvec, t0
  csrr a1, mtvec
  ori t0, t1, 1
  csrw mtvec, t0
  csrr a2, mtvec
  csrw mtvec, t1
  GUEST_EXIT(0)
GUEST_END
