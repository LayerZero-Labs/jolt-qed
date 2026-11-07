/* (b) ECALL from M with MIE = 1.
 * Spec (Sail): MPIE := MIE (= 1), MIE := 0, MPP := M.
 * Jolt: mstatus := 0x1800 (MPP = M, MPIE = 0, MIE = 0). */
#include "../common.h"
GUEST_START
  li t0, 8             /* MIE; Jolt does not decode CSRRSI */
  csrs mstatus, t0
  ecall
  GUEST_EXIT(1)
GUEST_END
