/* (h) The reserved RVC parcel 0x6001 (C.LUI with rd = x0 and nzimm = 0).
 * Spec (Sail): illegal-instruction trap (mcause 2, mtval 0x6001). Jolt
 * rejects it from 7c61100d8 on; before that it ran as a no-op. Jolt's
 * program-image decoder (RV64IMAC_JOLT) rejects the parcel when it loads an
 * image for proving. jolt-trace loads the ELF with Emulator::setup_program,
 * which decodes each instruction when it is first fetched, so the tracer
 * panics when it reaches the parcel. */
#include "../common.h"
GUEST_START
  .2byte 0x6001
  c.nop
  GUEST_EXIT(1)
GUEST_END
