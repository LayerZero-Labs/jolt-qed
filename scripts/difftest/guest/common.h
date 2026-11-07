/* Shared prologue and exit for difftest guests.
 *
 * Both simulators load the ELF at 0x80000000, start in M-mode at _start and
 * stop when the guest writes to `tohost` (HTIF). GUEST_START installs
 * `trap_handler` in mtvec, sets mstatus.MPP to M (so MRET stays in M-mode)
 * and zeroes the registers Sail's reset initialises (a0 = hart id,
 * a1 = device-tree address). The handler copies mcause, mepc, mtval and
 * mstatus into s2..s5 and exits with code 0.
 */
#define GUEST_START                 \
  .section .text.init;              \
  .globl _start;                    \
_start:                             \
  li a0, 0;                         \
  li a1, 0;                         \
  la t0, trap_handler;              \
  csrw mtvec, t0;                   \
  li t0, 0x1800;                    \
  csrs mstatus, t0;                 \
  li t0, 0;

/* Exit through HTIF with code CODE (0 = pass). */
#define GUEST_EXIT(CODE)            \
  li t6, ((CODE) << 1) | 1;         \
  la t5, tohost;                    \
  sd t6, 0(t5);                     \
1: j 1b;

#define GUEST_END                   \
  .align 2;                         \
trap_handler:                       \
  csrr s2, mcause;                  \
  csrr s3, mepc;                    \
  csrr s4, mtval;                   \
  csrr s5, mstatus;                 \
  GUEST_EXIT(0)                     \
  .section .tohost, "aw", @progbits;\
  .align 6;                         \
  .globl tohost;                    \
tohost: .dword 0;                   \
  .globl fromhost;                  \
fromhost: .dword 0;                 \
  .data;                            \
  .align 6;                         \
  .globl scratch;                   \
scratch: .dword 0x1111111111111111, 0x2222222222222222, 0x3333333333333333, 0x4444444444444444;
