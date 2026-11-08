/* (extra) CSRRC on mscratch. Jolt main (9407f93fb) decodes only CSRRW and
 * CSRRS among the Zicsr instructions; CSRRC, CSRRWI, CSRRSI and CSRRCI fail
 * to decode there. The random generator covers all six forms. */
#include "../common.h"
GUEST_START
  li t0, 0xff
  csrw mscratch, t0
  li t0, 0x0f
  csrc mscratch, t0
  csrr a0, mscratch
  GUEST_EXIT(0)
GUEST_END
