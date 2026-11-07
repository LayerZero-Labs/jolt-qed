/* (a) MRET from M with MPP = M, MPIE = 1, MIE = 0.
 * Spec (Sail): MIE := MPIE, MPIE := 1, MPP := least privileged mode (U here).
 * Jolt: MRET is JALR to mepc and leaves mstatus unchanged. */
#include "../common.h"
GUEST_START
  li t0, 0x80          /* MPIE */
  csrs mstatus, t0
  la t0, 2f
  csrw mepc, t0
  mret
2:
  csrr a0, mstatus
  GUEST_EXIT(0)
GUEST_END
