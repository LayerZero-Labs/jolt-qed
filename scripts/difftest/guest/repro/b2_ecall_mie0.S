/* (b, control) ECALL from M with MIE = 0: both sides should agree on
 * mstatus.MPIE/MIE/MPP. */
#include "../common.h"
GUEST_START
  ecall
  GUEST_EXIT(1)
GUEST_END
