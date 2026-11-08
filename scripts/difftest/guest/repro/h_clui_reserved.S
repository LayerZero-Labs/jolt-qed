/* (h) The reserved RVC parcel 0x6001 (C.LUI with rd = x0 and nzimm = 0).
 * Spec (Sail): illegal-instruction trap (mcause 2). Jolt rejects it from
 * 7c61100d8 on; before that it ran as a no-op. Jolt rejects such a parcel in
 * the ELF image when it loads the program, so this guest writes the parcel to
 * RAM after loading and jumps to it, where the tracer panics on it. There is
 * no FENCE.I, which Jolt does not decode; neither simulator caches fetches. */
#include "../common.h"
GUEST_START
  la t1, scratch
  li t2, 0x6001
  sh t2, 0(t1)
  jr t1
  GUEST_EXIT(1)
GUEST_END
