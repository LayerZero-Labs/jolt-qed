/* (c, consequence) Write mtvec with reserved MODE 2, then ECALL.
 * Sail keeps the old MODE, so the trap goes to the handler. Jolt main
 * (9407f93fb) stores the raw value and jumps to it with JALR, which clears
 * only bit 0. */
#include "../common.h"
GUEST_START
  la t1, trap_handler
  ori t0, t1, 2
  csrw mtvec, t0
  ecall
  GUEST_EXIT(1)
GUEST_END
