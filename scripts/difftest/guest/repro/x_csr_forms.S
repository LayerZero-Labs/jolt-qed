/* (extra) CSRRC on mscratch. Jolt decodes only CSRRW and CSRRS among the Zicsr
 * instructions; CSRRC, CSRRWI, CSRRSI and CSRRCI fail to decode. */
#include "../common.h"
GUEST_START
  li t0, 0xff
  csrw mscratch, t0
  li t0, 0x0f
  csrc mscratch, t0
  csrr a0, mscratch
  GUEST_EXIT(0)
GUEST_END
