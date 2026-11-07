import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.Xlen
import LeanRV64D.Types
import LeanRV64D.Callbacks
import LeanRV64D.Regs
import LeanRV64D.SysRegs
import LeanRV64D.ExtRegs
import LeanRV64D.InterruptRegs
import LeanRV64D.SysExceptions
import LeanRV64D.PmpRegs
import LeanRV64D.StateenRegs
import LeanRV64D.FdextRegs
import LeanRV64D.VextRegs
import LeanRV64D.Smcntrpmf
import LeanRV64D.SysControl
import LeanRV64D.InstsBegin
import LeanRV64D.ZkrControl

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

noncomputable section
namespace LeanRV64D

open ConcurrencyInterfaceV1

namespace Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zvabd_vwabda_func6
open zvabd_vabd_func6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_fault
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open biop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privilege
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open MemoryAccessType
open InterruptType
open ISA_Format
open HartState
open FetchResult
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

def encdec_csrop_backwards (arg_ : (BitVec 2)) : SailM csrop := do
  match arg_ with
  | 0b01 => (pure CSRRW)
  | 0b10 => (pure CSRRS)
  | 0b11 => (pure CSRRC)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_csrop_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | .CSRRW => true
  | .CSRRS => true
  | .CSRRC => true

def encdec_csrop_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

/-- Type quantifiers: k_ex256150_ : Bool, k_ex256149_ : Bool -/
def csr_access_type (op : csrop) (rd_is_x0 : Bool) (rs1_imm_is_zero : Bool) : CSRAccessType :=
  match (op, rd_is_x0, rs1_imm_is_zero) with
  | (.CSRRW, true, _) => CSRWrite
  | (.CSRRW, false, _) => CSRReadWrite
  | (.CSRRS, _, true) => CSRRead
  | (.CSRRC, _, true) => CSRRead
  | (.CSRRS, _, false) => CSRReadWrite
  | (.CSRRC, _, false) => CSRReadWrite

def _get_HpmEvent_OF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def get_scountovf (priv : Privilege) : SailM (BitVec 32) := do
  let overflow ← do
    (pure ((_get_HpmEvent_OF (GetElem?.getElem! (← readReg mhpmevent) 31)) +++ ((_get_HpmEvent_OF
            (GetElem?.getElem! (← readReg mhpmevent) 30)) +++ ((_get_HpmEvent_OF
              (GetElem?.getElem! (← readReg mhpmevent) 29)) +++ ((_get_HpmEvent_OF
                (GetElem?.getElem! (← readReg mhpmevent) 28)) +++ ((_get_HpmEvent_OF
                  (GetElem?.getElem! (← readReg mhpmevent) 27)) +++ ((_get_HpmEvent_OF
                    (GetElem?.getElem! (← readReg mhpmevent) 26)) +++ ((_get_HpmEvent_OF
                      (GetElem?.getElem! (← readReg mhpmevent) 25)) +++ ((_get_HpmEvent_OF
                        (GetElem?.getElem! (← readReg mhpmevent) 24)) +++ ((_get_HpmEvent_OF
                          (GetElem?.getElem! (← readReg mhpmevent) 23)) +++ ((_get_HpmEvent_OF
                            (GetElem?.getElem! (← readReg mhpmevent) 22)) +++ ((_get_HpmEvent_OF
                              (GetElem?.getElem! (← readReg mhpmevent) 21)) +++ ((_get_HpmEvent_OF
                                (GetElem?.getElem! (← readReg mhpmevent) 20)) +++ ((_get_HpmEvent_OF
                                  (GetElem?.getElem! (← readReg mhpmevent) 19)) +++ ((_get_HpmEvent_OF
                                    (GetElem?.getElem! (← readReg mhpmevent) 18)) +++ ((_get_HpmEvent_OF
                                      (GetElem?.getElem! (← readReg mhpmevent) 17)) +++ ((_get_HpmEvent_OF
                                        (GetElem?.getElem! (← readReg mhpmevent) 16)) +++ ((_get_HpmEvent_OF
                                          (GetElem?.getElem! (← readReg mhpmevent) 15)) +++ ((_get_HpmEvent_OF
                                            (GetElem?.getElem! (← readReg mhpmevent) 14)) +++ ((_get_HpmEvent_OF
                                              (GetElem?.getElem! (← readReg mhpmevent) 13)) +++ ((_get_HpmEvent_OF
                                                (GetElem?.getElem! (← readReg mhpmevent) 12)) +++ ((_get_HpmEvent_OF
                                                  (GetElem?.getElem! (← readReg mhpmevent) 11)) +++ ((_get_HpmEvent_OF
                                                    (GetElem?.getElem! (← readReg mhpmevent) 10)) +++ ((_get_HpmEvent_OF
                                                      (GetElem?.getElem! (← readReg mhpmevent) 9)) +++ ((_get_HpmEvent_OF
                                                        (GetElem?.getElem! (← readReg mhpmevent) 8)) +++ ((_get_HpmEvent_OF
                                                          (GetElem?.getElem! (← readReg mhpmevent)
                                                            7)) +++ ((_get_HpmEvent_OF
                                                            (GetElem?.getElem!
                                                              (← readReg mhpmevent) 6)) +++ ((_get_HpmEvent_OF
                                                              (GetElem?.getElem!
                                                                (← readReg mhpmevent) 5)) +++ ((_get_HpmEvent_OF
                                                                (GetElem?.getElem!
                                                                  (← readReg mhpmevent) 4)) +++ ((_get_HpmEvent_OF
                                                                  (GetElem?.getElem!
                                                                    (← readReg mhpmevent) 3)) +++ 0b000#3))))))))))))))))))))))))))))))
  match priv with
  | .Machine => (pure overflow)
  | .Supervisor => (pure (overflow &&& (← readReg mcounteren)))
  | .User =>
    (internal_error "extensions/Sscofpmf/sscofpmf.sail" 74 "scountovf not readable from User mode")
  | .VirtualUser =>
    (internal_error "extensions/Sscofpmf/sscofpmf.sail" 75 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/Sscofpmf/sscofpmf.sail" 76 "Hypervisor extension not supported")

def hpmidx_from_bits (b : (BitVec 5)) : SailM Nat := do
  let index := (BitVec.toNatInt b)
  sail_assert (index ≥b 3) "unreachable HPM index"
  (pure index)

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmcounter (index : Nat) : SailM (BitVec 64) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmcounter) index) (xlen -i 1) 0))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmcounterh (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmcounter) index) 63 32))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmevent (index : Nat) : SailM (BitVec 64) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) (xlen -i 1) 0))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmeventh (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) 63 32))

def read_CSR (b__0 : (BitVec 12)) : SailM (BitVec 64) := do
  if ((b__0 == (0x301#12 : (BitVec 12))) : Bool)
  then readReg misa
  else
    (do
      if ((b__0 == (0x300#12 : (BitVec 12))) : Bool)
      then (pure (Sail.BitVec.extractLsb (← readReg mstatus) (xlen -i 1) 0))
      else
        (do
          if (((b__0 == (0x310#12 : (BitVec 12))) && (xlen == 32)) : Bool)
          then (pure (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))
          else
            (do
              if ((b__0 == (0x747#12 : (BitVec 12))) : Bool)
              then (pure (Sail.BitVec.extractLsb (← readReg mseccfg) (xlen -i 1) 0))
              else
                (do
                  if (((b__0 == (0x757#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                  then (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))
                  else
                    (do
                      if ((b__0 == (0x30A#12 : (BitVec 12))) : Bool)
                      then (pure (Sail.BitVec.extractLsb (← readReg menvcfg) (xlen -i 1) 0))
                      else
                        (do
                          if (((b__0 == (0x31A#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                          then (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))
                          else
                            (do
                              if ((b__0 == (0x10A#12 : (BitVec 12))) : Bool)
                              then (read_senvcfg ())
                              else
                                (do
                                  if ((b__0 == (0x342#12 : (BitVec 12))) : Bool)
                                  then readReg mcause
                                  else
                                    (do
                                      if ((b__0 == (0x343#12 : (BitVec 12))) : Bool)
                                      then readReg mtval
                                      else
                                        (do
                                          if ((b__0 == (0x340#12 : (BitVec 12))) : Bool)
                                          then readReg mscratch
                                          else
                                            (do
                                              if ((b__0 == (0x106#12 : (BitVec 12))) : Bool)
                                              then
                                                (pure (zero_extend (m := 64)
                                                    (← readReg scounteren)))
                                              else
                                                (do
                                                  if ((b__0 == (0x306#12 : (BitVec 12))) : Bool)
                                                  then
                                                    (pure (zero_extend (m := 64)
                                                        (← readReg mcounteren)))
                                                  else
                                                    (do
                                                      if ((b__0 == (0x320#12 : (BitVec 12))) : Bool)
                                                      then
                                                        (pure (zero_extend (m := 64)
                                                            (← readReg mcountinhibit)))
                                                      else
                                                        (do
                                                          if ((b__0 == (0xF11#12 : (BitVec 12))) : Bool)
                                                          then
                                                            (pure (zero_extend (m := 64)
                                                                (← readReg mvendorid)))
                                                          else
                                                            (do
                                                              if ((b__0 == (0xF12#12 : (BitVec 12))) : Bool)
                                                              then readReg marchid
                                                              else
                                                                (do
                                                                  if ((b__0 == (0xF13#12 : (BitVec 12))) : Bool)
                                                                  then readReg mimpid
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0xF14#12 : (BitVec 12))) : Bool)
                                                                      then readReg mhartid
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0xF15#12 : (BitVec 12))) : Bool)
                                                                          then readReg mconfigptr
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0x100#12 : (BitVec 12))) : Bool)
                                                                              then
                                                                                (pure (Sail.BitVec.extractLsb
                                                                                    (lower_mstatus
                                                                                      (← readReg mstatus))
                                                                                    (xlen -i 1) 0))
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0x140#12 : (BitVec 12))) : Bool)
                                                                                  then
                                                                                    readReg sscratch
                                                                                  else
                                                                                    (do
                                                                                      if ((b__0 == (0x142#12 : (BitVec 12))) : Bool)
                                                                                      then
                                                                                        readReg scause
                                                                                      else
                                                                                        (do
                                                                                          if ((b__0 == (0x143#12 : (BitVec 12))) : Bool)
                                                                                          then
                                                                                            readReg stval
                                                                                          else
                                                                                            (do
                                                                                              if ((b__0 == (0x7A0#12 : (BitVec 12))) : Bool)
                                                                                              then
                                                                                                (pure (Complement.complement
                                                                                                    (← readReg tselect)))
                                                                                              else
                                                                                                (do
                                                                                                  if ((b__0 == (0x304#12 : (BitVec 12))) : Bool)
                                                                                                  then
                                                                                                    readReg mie
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((b__0 == (0x344#12 : (BitVec 12))) : Bool)
                                                                                                      then
                                                                                                        readReg mip
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((b__0 == (0x302#12 : (BitVec 12))) : Bool)
                                                                                                          then
                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                (← readReg medeleg)
                                                                                                                (xlen -i 1)
                                                                                                                0))
                                                                                                          else
                                                                                                            (do
                                                                                                              if (((b__0 == (0x312#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                              then
                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                    (← readReg medeleg)
                                                                                                                    63
                                                                                                                    32))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0x303#12 : (BitVec 12))) : Bool)
                                                                                                                  then
                                                                                                                    readReg mideleg
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((b__0 == (0x144#12 : (BitVec 12))) : Bool)
                                                                                                                      then
                                                                                                                        (pure (lower_mip
                                                                                                                            (← readReg mip)
                                                                                                                            (← readReg mideleg)))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((b__0 == (0x104#12 : (BitVec 12))) : Bool)
                                                                                                                          then
                                                                                                                            (pure (lower_mie
                                                                                                                                (← readReg mie)
                                                                                                                                (← readReg mideleg)))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((b__0 == (0x105#12 : (BitVec 12))) : Bool)
                                                                                                                              then
                                                                                                                                (get_stvec
                                                                                                                                  ())
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((b__0 == (0x141#12 : (BitVec 12))) : Bool)
                                                                                                                                  then
                                                                                                                                    (get_xepc
                                                                                                                                      Supervisor)
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((b__0 == (0x305#12 : (BitVec 12))) : Bool)
                                                                                                                                      then
                                                                                                                                        (get_mtvec
                                                                                                                                          ())
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((b__0 == (0x341#12 : (BitVec 12))) : Bool)
                                                                                                                                          then
                                                                                                                                            (get_xepc
                                                                                                                                              Machine)
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                       b__0
                                                                                                                                                       11
                                                                                                                                                       4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                       b__0
                                                                                                                                                       3
                                                                                                                                                       0)
                                                                                                                                                   (((BitVec.access
                                                                                                                                                         idx
                                                                                                                                                         0) == 0#1) || (xlen == 32)))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                      b__0
                                                                                                                                                      3
                                                                                                                                                      0)
                                                                                                                                                  (pmpReadCfgReg
                                                                                                                                                    (BitVec.toNatInt
                                                                                                                                                      idx)))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                                                                         b__0
                                                                                                                                                         11
                                                                                                                                                         4) == (0x3B#8 : (BitVec 8))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      let idx : (BitVec 4) :=
                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                          b__0
                                                                                                                                                          3
                                                                                                                                                          0)
                                                                                                                                                      (pmpReadAddrReg
                                                                                                                                                        (BitVec.toNatInt
                                                                                                                                                          (0b00#2 +++ idx))))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if (((Sail.BitVec.extractLsb
                                                                                                                                                             b__0
                                                                                                                                                             11
                                                                                                                                                             4) == (0x3C#8 : (BitVec 8))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          let idx : (BitVec 4) :=
                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                              b__0
                                                                                                                                                              3
                                                                                                                                                              0)
                                                                                                                                                          (pmpReadAddrReg
                                                                                                                                                            (BitVec.toNatInt
                                                                                                                                                              (0b01#2 +++ idx))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                                                                                 b__0
                                                                                                                                                                 11
                                                                                                                                                                 4) == (0x3D#8 : (BitVec 8))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                  b__0
                                                                                                                                                                  3
                                                                                                                                                                  0)
                                                                                                                                                              (pmpReadAddrReg
                                                                                                                                                                (BitVec.toNatInt
                                                                                                                                                                  (0b10#2 +++ idx))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                                     b__0
                                                                                                                                                                     11
                                                                                                                                                                     4) == (0x3E#8 : (BitVec 8))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                      b__0
                                                                                                                                                                      3
                                                                                                                                                                      0)
                                                                                                                                                                  (pmpReadAddrReg
                                                                                                                                                                    (BitVec.toNatInt
                                                                                                                                                                      (0b11#2 +++ idx))))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((b__0 == (0x001#12 : (BitVec 12))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (pure (zero_extend
                                                                                                                                                                        (m := 64)
                                                                                                                                                                        (_get_Fcsr_FFLAGS
                                                                                                                                                                          (← readReg fcsr))))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((b__0 == (0x002#12 : (BitVec 12))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (pure (zero_extend
                                                                                                                                                                            (m := 64)
                                                                                                                                                                            (_get_Fcsr_FRM
                                                                                                                                                                              (← readReg fcsr))))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((b__0 == (0x003#12 : (BitVec 12))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (pure (zero_extend
                                                                                                                                                                                (m := 64)
                                                                                                                                                                                (← readReg fcsr)))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((b__0 == (0x008#12 : (BitVec 12))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                readReg vstart
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((b__0 == (0x009#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (pure (zero_extend
                                                                                                                                                                                        (m := 64)
                                                                                                                                                                                        (_get_Vcsr_vxsat
                                                                                                                                                                                          (← readReg vcsr))))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((b__0 == (0x00A#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (pure (zero_extend
                                                                                                                                                                                            (m := 64)
                                                                                                                                                                                            (_get_Vcsr_vxrm
                                                                                                                                                                                              (← readReg vcsr))))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((b__0 == (0x00F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (pure (zero_extend
                                                                                                                                                                                                (m := 64)
                                                                                                                                                                                                (← readReg vcsr)))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((b__0 == (0xC20#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                readReg vl
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((b__0 == (0xC21#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    readReg vtype
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((b__0 == (0xC22#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (pure VLENB)
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((b__0 == (0x321#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                (← readReg mcyclecfg)
                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                0))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if (((b__0 == (0x721#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                    (← readReg mcyclecfg)
                                                                                                                                                                                                                    63
                                                                                                                                                                                                                    32))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((b__0 == (0x322#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                        (← readReg minstretcfg)
                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if (((b__0 == (0x722#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                            (← readReg minstretcfg)
                                                                                                                                                                                                                            63
                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((b__0 == (0x30C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                (← readReg mstateen0)
                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                0))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((b__0 == (0x30D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    (← readReg mstateen1)
                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                    0))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((b__0 == (0x30E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        (← readReg mstateen2)
                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((b__0 == (0x30F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                            (← readReg mstateen3)
                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                            0))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if (((b__0 == (0x31C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                (← readReg mstateen0)
                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                32))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if (((b__0 == (0x31D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                    (← readReg mstateen1)
                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if (((b__0 == (0x31E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                        (← readReg mstateen2)
                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                        32))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if (((b__0 == (0x31F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                            (← readReg mstateen3)
                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((b__0 == (0x60C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                ((← readReg hstateen0) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                      0)))
                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                0))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((b__0 == (0x60D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                          1)))
                                                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                                                    0))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((b__0 == (0x60E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                              2)))
                                                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((b__0 == (0x60F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            ((← readReg hstateen3) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                                  3)))
                                                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                                                            0))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if (((b__0 == (0x61C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                ((← readReg hstateen0) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                                      0)))
                                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                                32))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if (((b__0 == (0x61D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                    ((← readReg hstateen1) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                                          1)))
                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if (((b__0 == (0x61E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                        ((← readReg hstateen2) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                                              2)))
                                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                                        32))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if (((b__0 == (0x61F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                            ((← readReg hstateen3) &&& (← (get_hstateen_mask
                                                                                                                                                                                                                                                                                                  3)))
                                                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((b__0 == (0x10C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              let mask ← do
                                                                                                                                                                                                                                                                                                (get_sstateen_mask
                                                                                                                                                                                                                                                                                                  0)
                                                                                                                                                                                                                                                                                              (pure (zero_extend
                                                                                                                                                                                                                                                                                                  (m := 64)
                                                                                                                                                                                                                                                                                                  ((← readReg sstateen0) &&& (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                      mask
                                                                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                                                                      0)))))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((b__0 == (0x10D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  let mask ← do
                                                                                                                                                                                                                                                                                                    (get_sstateen_mask
                                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                                  (pure (zero_extend
                                                                                                                                                                                                                                                                                                      (m := 64)
                                                                                                                                                                                                                                                                                                      ((← readReg sstateen1) &&& (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                          mask
                                                                                                                                                                                                                                                                                                          31
                                                                                                                                                                                                                                                                                                          0)))))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x10E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      let mask ← do
                                                                                                                                                                                                                                                                                                        (get_sstateen_mask
                                                                                                                                                                                                                                                                                                          2)
                                                                                                                                                                                                                                                                                                      (pure (zero_extend
                                                                                                                                                                                                                                                                                                          (m := 64)
                                                                                                                                                                                                                                                                                                          ((← readReg sstateen2) &&& (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                              mask
                                                                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                                                                              0)))))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x10F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          let mask ← do
                                                                                                                                                                                                                                                                                                            (get_sstateen_mask
                                                                                                                                                                                                                                                                                                              3)
                                                                                                                                                                                                                                                                                                          (pure (zero_extend
                                                                                                                                                                                                                                                                                                              (m := 64)
                                                                                                                                                                                                                                                                                                              ((← readReg sstateen3) &&& (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                  mask
                                                                                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                                                                                  0)))))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x180#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            readReg satp
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x015#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (read_seed_csr
                                                                                                                                                                                                                                                                                                                  ())
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                                                                                           5) == (0b0011001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                                                                                       ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                                                                                      (read_mhpmevent
                                                                                                                                                                                                                                                                                                                        (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                            index))))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                                                                                               5) == (0b1011000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                                                                                                           ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                               index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                              b__0
                                                                                                                                                                                                                                                                                                                              4
                                                                                                                                                                                                                                                                                                                              0)
                                                                                                                                                                                                                                                                                                                          (read_mhpmcounter
                                                                                                                                                                                                                                                                                                                            (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                index))))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                                                                                   11
                                                                                                                                                                                                                                                                                                                                   5) == (0b1011100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                                                                                   4
                                                                                                                                                                                                                                                                                                                                   0)
                                                                                                                                                                                                                                                                                                                               ((xlen == 32) && (((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                     index) ≥b 3) : Bool)))) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                  b__0
                                                                                                                                                                                                                                                                                                                                  4
                                                                                                                                                                                                                                                                                                                                  0)
                                                                                                                                                                                                                                                                                                                              (read_mhpmcounterh
                                                                                                                                                                                                                                                                                                                                (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                    index))))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                       11
                                                                                                                                                                                                                                                                                                                                       5) == (0b1100000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                                                                                                                                   ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                       index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                      b__0
                                                                                                                                                                                                                                                                                                                                      4
                                                                                                                                                                                                                                                                                                                                      0)
                                                                                                                                                                                                                                                                                                                                  (read_mhpmcounter
                                                                                                                                                                                                                                                                                                                                    (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                        index))))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                                                                                                           5) == (0b1100100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                                                                                                       ((xlen == 32) && (((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                             index) ≥b 3) : Bool)))) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                                                                                                      (read_mhpmcounterh
                                                                                                                                                                                                                                                                                                                                        (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                            index))))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                                                                                                               5) == (0b0111001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                                                                                                                           ((xlen == 32) && (((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                 index) ≥b 3) : Bool)))) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                              b__0
                                                                                                                                                                                                                                                                                                                                              4
                                                                                                                                                                                                                                                                                                                                              0)
                                                                                                                                                                                                                                                                                                                                          (read_mhpmeventh
                                                                                                                                                                                                                                                                                                                                            (← (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                                index))))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xDA0#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (pure (zero_extend
                                                                                                                                                                                                                                                                                                                                                (m := 64)
                                                                                                                                                                                                                                                                                                                                                (← (get_scountovf
                                                                                                                                                                                                                                                                                                                                                    (← readReg cur_privilege)))))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x14D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                    (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                    0))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if (((b__0 == (0x15D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                        (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                                                                                                        32))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x011#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        readReg ssp
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xC00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                0))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xC01#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                    (← readReg mtime)
                                                                                                                                                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                    0))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                        (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if (((b__0 == (0xC80#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                            (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if (((b__0 == (0xC81#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                (← readReg mtime)
                                                                                                                                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                                                                                                                                32))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if (((b__0 == (0xC82#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                    (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xB00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                        (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xB02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                            (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                                            0))
                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                          if (((b__0 == (0xB80#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                                                                                                                                                32))
                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                              if (((b__0 == (0xB82#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                    (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x181#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                    readReg srmcfg
                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                    (internal_error
                                                                                                                                                                                                                                                                                                                                                                                                      "postlude/csr_end.sail"
                                                                                                                                                                                                                                                                                                                                                                                                      17
                                                                                                                                                                                                                                                                                                                                                                                                      (HAppend.hAppend
                                                                                                                                                                                                                                                                                                                                                                                                        "Read from CSR that does not exist: "
                                                                                                                                                                                                                                                                                                                                                                                                        (BitVec.toFormatted
                                                                                                                                                                                                                                                                                                                                                                                                          b__0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def Mk_Srmcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Srmcfg_MCID (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_Srmcfg_RCID (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 27 16)

def _update_Srmcfg_MCID (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_Srmcfg_RCID (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 16 x)

def mcidlen : Nat := 12

def rcidlen : Nat := 12

def legalize_srmcfg (o : (BitVec 64)) (value : (BitVec 64)) : (BitVec 64) :=
  let v := (Mk_Srmcfg value)
  let rcid_mask : (BitVec 12) := (zero_extend (m := 12) (ones (n := rcidlen)))
  let mcid_mask : (BitVec 12) := (zero_extend (m := 12) (ones (n := mcidlen)))
  (_update_Srmcfg_MCID (_update_Srmcfg_RCID o ((_get_Srmcfg_RCID v) &&& rcid_mask))
    ((_get_Srmcfg_MCID v) &&& mcid_mask))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmcounter (index : Nat) (value : (BitVec 64)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    writeReg mhpmcounter (vectorUpdate (← readReg mhpmcounter) index
      (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg mhpmcounter) index) (xlen -i 1) 0
        value))
  else (pure ())

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmcounterh (index : Nat) (value : (BitVec 32)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    writeReg mhpmcounter (vectorUpdate (← readReg mhpmcounter) index
      (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg mhpmcounter) index) 63 32 value))
  else (pure ())

def Mk_HpmEvent (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HpmEvent_event (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_HpmEvent_OF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_HpmEvent_event (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def legalize_hpmevent (v : (BitVec 64)) : SailM (BitVec 64) := do
  (pure (_update_HpmEvent_event
      (_update_HpmEvent_VUINH
        (_update_HpmEvent_VSINH
          (_update_HpmEvent_UINH
            (_update_HpmEvent_SINH
              (_update_HpmEvent_MINH
                (_update_HpmEvent_OF (Mk_HpmEvent (zeros (n := 64)))
                  (← do
                    if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                    then (pure (_get_HpmEvent_OF v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                  then (pure (_get_HpmEvent_MINH v))
                  else (pure 0#1)))
              (← do
                if ((←((currentlyEnabled Ext_Sscofpmf) <&&> (do
                     (currentlyEnabled Ext_S)))) : Bool)
                then (pure (_get_HpmEvent_SINH v))
                else (pure 0#1)))
            (← do
              if ((←((currentlyEnabled Ext_Sscofpmf) <&&> (do
                   (currentlyEnabled Ext_U)))) : Bool)
              then (pure (_get_HpmEvent_UINH v))
              else (pure 0#1))) 0#1) 0#1) (_get_HpmEvent_event v)))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmevent (index : Nat) (value : (BitVec 64)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    writeReg mhpmevent (vectorUpdate (← readReg mhpmevent) index
      (← (legalize_hpmevent
          (Mk_HpmEvent
            (← do
              match xlen with
              | 64 => (pure value)
              | _ => (internal_error "extensions/Zihpm/zihpm.sail" 223 "Unsupported xlen"))))))
  else (pure ())

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmeventh (index : Nat) (value : (BitVec 32)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    writeReg mhpmevent (vectorUpdate (← readReg mhpmevent) index
      (← (legalize_hpmevent
          (Mk_HpmEvent
            (value +++ (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) 31
                0))))))
  else (pure ())

def write_CSR (b__0 : (BitVec 12)) (value : (BitVec 64)) : SailM (Result (BitVec 64) Unit) := do
  if ((b__0 == (0x301#12 : (BitVec 12))) : Bool)
  then
    (do
      writeReg misa (← (legalize_misa (← readReg misa) value))
      (pure (Ok (← readReg misa))))
  else
    (do
      if (((b__0 == (0x300#12 : (BitVec 12))) && (xlen == 64)) : Bool)
      then
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus) value))
          (pure (Ok (← readReg mstatus))))
      else
        (do
          if (((b__0 == (0x300#12 : (BitVec 12))) && (xlen == 32)) : Bool)
          then
            (do
              writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
                  ((Sail.BitVec.extractLsb (← readReg mstatus) 63 32) +++ value)))
              (pure (Ok (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))
          else
            (do
              if (((b__0 == (0x310#12 : (BitVec 12))) && (xlen == 32)) : Bool)
              then
                (do
                  writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
                      (value +++ (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))
                  (pure (Ok (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))))
              else
                (do
                  if (((b__0 == (0x747#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                  then
                    (do
                      writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
                          ((Sail.BitVec.extractLsb (← readReg mseccfg) 63 32) +++ value)))
                      (pure (Ok (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
                  else
                    (do
                      if (((b__0 == (0x747#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                      then
                        (do
                          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg) value))
                          (pure (Ok (← readReg mseccfg))))
                      else
                        (do
                          if (((b__0 == (0x757#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                          then
                            (do
                              writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
                                  (value +++ (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
                              (pure (Ok (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))))
                          else
                            (do
                              if (((b__0 == (0x30A#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                              then
                                (do
                                  writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
                                      ((Sail.BitVec.extractLsb (← readReg menvcfg) 63 32) +++ value)))
                                  (pure (Ok (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0))))
                              else
                                (do
                                  if (((b__0 == (0x30A#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                  then
                                    (do
                                      writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
                                          value))
                                      (pure (Ok (← readReg menvcfg))))
                                  else
                                    (do
                                      if (((b__0 == (0x31A#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                      then
                                        (do
                                          writeReg menvcfg (← (legalize_menvcfg
                                              (← readReg menvcfg)
                                              (value +++ (Sail.BitVec.extractLsb
                                                  (← readReg menvcfg) 31 0))))
                                          (pure (Ok
                                              (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))))
                                      else
                                        (do
                                          if ((b__0 == (0x10A#12 : (BitVec 12))) : Bool)
                                          then
                                            (do
                                              writeReg senvcfg (← (legalize_senvcfg
                                                  (← readReg senvcfg)
                                                  (zero_extend (m := 64) value)))
                                              (pure (Ok (← (read_senvcfg ())))))
                                          else
                                            (do
                                              if ((b__0 == (0x342#12 : (BitVec 12))) : Bool)
                                              then
                                                (do
                                                  writeReg mcause value
                                                  (pure (Ok (← readReg mcause))))
                                              else
                                                (do
                                                  if ((b__0 == (0x343#12 : (BitVec 12))) : Bool)
                                                  then
                                                    (do
                                                      writeReg mtval value
                                                      (pure (Ok (← readReg mtval))))
                                                  else
                                                    (do
                                                      if ((b__0 == (0x340#12 : (BitVec 12))) : Bool)
                                                      then
                                                        (do
                                                          writeReg mscratch value
                                                          (pure (Ok (← readReg mscratch))))
                                                      else
                                                        (do
                                                          if ((b__0 == (0x106#12 : (BitVec 12))) : Bool)
                                                          then
                                                            (do
                                                              writeReg scounteren (legalize_scounteren
                                                                (← readReg scounteren) value)
                                                              (pure (Ok
                                                                  (zero_extend (m := 64)
                                                                    (← readReg scounteren)))))
                                                          else
                                                            (do
                                                              if ((b__0 == (0x306#12 : (BitVec 12))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg mcounteren (legalize_mcounteren
                                                                    (← readReg mcounteren) value)
                                                                  (pure (Ok
                                                                      (zero_extend (m := 64)
                                                                        (← readReg mcounteren)))))
                                                              else
                                                                (do
                                                                  if ((b__0 == (0x320#12 : (BitVec 12))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg mcountinhibit (legalize_mcountinhibit
                                                                        (← readReg mcountinhibit)
                                                                        value)
                                                                      (pure (Ok
                                                                          (zero_extend (m := 64)
                                                                            (← readReg mcountinhibit)))))
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0x100#12 : (BitVec 12))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg mstatus (← (legalize_sstatus
                                                                              (← readReg mstatus)
                                                                              value))
                                                                          (pure (Ok
                                                                              (Sail.BitVec.extractLsb
                                                                                (lower_mstatus
                                                                                  (← readReg mstatus))
                                                                                (xlen -i 1) 0))))
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0x140#12 : (BitVec 12))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg sscratch value
                                                                              (pure (Ok
                                                                                  (← readReg sscratch))))
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0x142#12 : (BitVec 12))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg scause value
                                                                                  (pure (Ok
                                                                                      (← readReg scause))))
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0x143#12 : (BitVec 12))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg stval value
                                                                                      (pure (Ok
                                                                                          (← readReg stval))))
                                                                                  else
                                                                                    (do
                                                                                      if ((b__0 == (0x7A0#12 : (BitVec 12))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg tselect value
                                                                                          (pure (Ok
                                                                                              (← readReg tselect))))
                                                                                      else
                                                                                        (do
                                                                                          if ((b__0 == (0x304#12 : (BitVec 12))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg mie (← (legalize_mie
                                                                                                  (← readReg mie)
                                                                                                  value))
                                                                                              (pure (Ok
                                                                                                  (← readReg mie))))
                                                                                          else
                                                                                            (do
                                                                                              if ((b__0 == (0x344#12 : (BitVec 12))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg mip (← (legalize_mip
                                                                                                      (← readReg mip)
                                                                                                      value))
                                                                                                  (pure (Ok
                                                                                                      (← readReg mip))))
                                                                                              else
                                                                                                (do
                                                                                                  if (((b__0 == (0x302#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg medeleg (legalize_medeleg
                                                                                                        (← readReg medeleg)
                                                                                                        value)
                                                                                                      (pure (Ok
                                                                                                          (← readReg medeleg))))
                                                                                                  else
                                                                                                    (do
                                                                                                      if (((b__0 == (0x302#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg medeleg (legalize_medeleg
                                                                                                            (← readReg medeleg)
                                                                                                            ((Sail.BitVec.extractLsb
                                                                                                                (← readReg medeleg)
                                                                                                                63
                                                                                                                32) +++ value))
                                                                                                          (pure (Ok
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                (← readReg medeleg)
                                                                                                                31
                                                                                                                0))))
                                                                                                      else
                                                                                                        (do
                                                                                                          if (((b__0 == (0x312#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg medeleg (legalize_medeleg
                                                                                                                (← readReg medeleg)
                                                                                                                (value +++ (Sail.BitVec.extractLsb
                                                                                                                    (← readReg medeleg)
                                                                                                                    31
                                                                                                                    0)))
                                                                                                              (pure (Ok
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    (← readReg medeleg)
                                                                                                                    63
                                                                                                                    32))))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((b__0 == (0x303#12 : (BitVec 12))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg mideleg (← (legalize_mideleg
                                                                                                                      (← readReg mideleg)
                                                                                                                      value))
                                                                                                                  (pure (Ok
                                                                                                                      (← readReg mideleg))))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0x144#12 : (BitVec 12))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg mip (legalize_sip
                                                                                                                        (← readReg mip)
                                                                                                                        (← readReg mideleg)
                                                                                                                        value)
                                                                                                                      (pure (Ok
                                                                                                                          (lower_mip
                                                                                                                            (← readReg mip)
                                                                                                                            (← readReg mideleg)))))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((b__0 == (0x104#12 : (BitVec 12))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg mie (legalize_sie
                                                                                                                            (← readReg mie)
                                                                                                                            (← readReg mideleg)
                                                                                                                            value)
                                                                                                                          (pure (Ok
                                                                                                                              (lower_mie
                                                                                                                                (← readReg mie)
                                                                                                                                (← readReg mideleg)))))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((b__0 == (0x105#12 : (BitVec 12))) : Bool)
                                                                                                                          then
                                                                                                                            (pure (Ok
                                                                                                                                (← (set_stvec
                                                                                                                                    value))))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((b__0 == (0x141#12 : (BitVec 12))) : Bool)
                                                                                                                              then
                                                                                                                                (pure (Ok
                                                                                                                                    (← (set_xepc
                                                                                                                                        Supervisor
                                                                                                                                        value))))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((b__0 == (0x305#12 : (BitVec 12))) : Bool)
                                                                                                                                  then
                                                                                                                                    (pure (Ok
                                                                                                                                        (← (set_mtvec
                                                                                                                                            value))))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((b__0 == (0x341#12 : (BitVec 12))) : Bool)
                                                                                                                                      then
                                                                                                                                        (pure (Ok
                                                                                                                                            (← (set_xepc
                                                                                                                                                Machine
                                                                                                                                                value))))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((Sail.BitVec.extractLsb
                                                                                                                                                   b__0
                                                                                                                                                   11
                                                                                                                                                   4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                   b__0
                                                                                                                                                   3
                                                                                                                                                   0)
                                                                                                                                               (((BitVec.access
                                                                                                                                                     idx
                                                                                                                                                     0) == 0#1) || (xlen == 32)))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                  b__0
                                                                                                                                                  3
                                                                                                                                                  0)
                                                                                                                                              let idx :=
                                                                                                                                                (BitVec.toNatInt
                                                                                                                                                  idx)
                                                                                                                                              (pmpWriteCfgReg
                                                                                                                                                idx
                                                                                                                                                value)
                                                                                                                                              (pure (Ok
                                                                                                                                                  (← (pmpReadCfgReg
                                                                                                                                                      idx)))))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                     b__0
                                                                                                                                                     11
                                                                                                                                                     4) == (0x3B#8 : (BitVec 8))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                      b__0
                                                                                                                                                      3
                                                                                                                                                      0)
                                                                                                                                                  let idx :=
                                                                                                                                                    (BitVec.toNatInt
                                                                                                                                                      (0b00#2 +++ idx))
                                                                                                                                                  (pmpWriteAddrReg
                                                                                                                                                    idx
                                                                                                                                                    value)
                                                                                                                                                  (pure (Ok
                                                                                                                                                      (← (pmpReadAddrReg
                                                                                                                                                          idx)))))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                                                                         b__0
                                                                                                                                                         11
                                                                                                                                                         4) == (0x3C#8 : (BitVec 8))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      let idx : (BitVec 4) :=
                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                          b__0
                                                                                                                                                          3
                                                                                                                                                          0)
                                                                                                                                                      let idx :=
                                                                                                                                                        (BitVec.toNatInt
                                                                                                                                                          (0b01#2 +++ idx))
                                                                                                                                                      (pmpWriteAddrReg
                                                                                                                                                        idx
                                                                                                                                                        value)
                                                                                                                                                      (pure (Ok
                                                                                                                                                          (← (pmpReadAddrReg
                                                                                                                                                              idx)))))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if (((Sail.BitVec.extractLsb
                                                                                                                                                             b__0
                                                                                                                                                             11
                                                                                                                                                             4) == (0x3D#8 : (BitVec 8))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          let idx : (BitVec 4) :=
                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                              b__0
                                                                                                                                                              3
                                                                                                                                                              0)
                                                                                                                                                          let idx :=
                                                                                                                                                            (BitVec.toNatInt
                                                                                                                                                              (0b10#2 +++ idx))
                                                                                                                                                          (pmpWriteAddrReg
                                                                                                                                                            idx
                                                                                                                                                            value)
                                                                                                                                                          (pure (Ok
                                                                                                                                                              (← (pmpReadAddrReg
                                                                                                                                                                  idx)))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                                                                                 b__0
                                                                                                                                                                 11
                                                                                                                                                                 4) == (0x3E#8 : (BitVec 8))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                  b__0
                                                                                                                                                                  3
                                                                                                                                                                  0)
                                                                                                                                                              let idx :=
                                                                                                                                                                (BitVec.toNatInt
                                                                                                                                                                  (0b11#2 +++ idx))
                                                                                                                                                              (pmpWriteAddrReg
                                                                                                                                                                idx
                                                                                                                                                                value)
                                                                                                                                                              (pure (Ok
                                                                                                                                                                  (← (pmpReadAddrReg
                                                                                                                                                                      idx)))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((b__0 == (0x001#12 : (BitVec 12))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (write_fcsr
                                                                                                                                                                    (_get_Fcsr_FRM
                                                                                                                                                                      (← readReg fcsr))
                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                      value
                                                                                                                                                                      4
                                                                                                                                                                      0))
                                                                                                                                                                  (pure (Ok
                                                                                                                                                                      (zero_extend
                                                                                                                                                                        (m := 64)
                                                                                                                                                                        (_get_Fcsr_FFLAGS
                                                                                                                                                                          (← readReg fcsr))))))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((b__0 == (0x002#12 : (BitVec 12))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (write_fcsr
                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                          value
                                                                                                                                                                          2
                                                                                                                                                                          0)
                                                                                                                                                                        (_get_Fcsr_FFLAGS
                                                                                                                                                                          (← readReg fcsr)))
                                                                                                                                                                      (pure (Ok
                                                                                                                                                                          (zero_extend
                                                                                                                                                                            (m := 64)
                                                                                                                                                                            (_get_Fcsr_FRM
                                                                                                                                                                              (← readReg fcsr))))))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((b__0 == (0x003#12 : (BitVec 12))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (write_fcsr
                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                              value
                                                                                                                                                                              7
                                                                                                                                                                              5)
                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                              value
                                                                                                                                                                              4
                                                                                                                                                                              0))
                                                                                                                                                                          (pure (Ok
                                                                                                                                                                              (zero_extend
                                                                                                                                                                                (m := 64)
                                                                                                                                                                                (← readReg fcsr)))))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((b__0 == (0x008#12 : (BitVec 12))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (set_vstart
                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                  value
                                                                                                                                                                                  15
                                                                                                                                                                                  0))
                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                  (← readReg vstart))))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((b__0 == (0x009#12 : (BitVec 12))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (write_vcsr
                                                                                                                                                                                    (_get_Vcsr_vxrm
                                                                                                                                                                                      (← readReg vcsr))
                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                      value
                                                                                                                                                                                      0
                                                                                                                                                                                      0))
                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                      (zero_extend
                                                                                                                                                                                        (m := 64)
                                                                                                                                                                                        (_get_Vcsr_vxsat
                                                                                                                                                                                          (← readReg vcsr))))))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((b__0 == (0x00A#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (write_vcsr
                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                          value
                                                                                                                                                                                          1
                                                                                                                                                                                          0)
                                                                                                                                                                                        (_get_Vcsr_vxsat
                                                                                                                                                                                          (← readReg vcsr)))
                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                          (zero_extend
                                                                                                                                                                                            (m := 64)
                                                                                                                                                                                            (_get_Vcsr_vxrm
                                                                                                                                                                                              (← readReg vcsr))))))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((b__0 == (0x00F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (write_vcsr
                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                              value
                                                                                                                                                                                              2
                                                                                                                                                                                              1)
                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                              value
                                                                                                                                                                                              0
                                                                                                                                                                                              0))
                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                              (zero_extend
                                                                                                                                                                                                (m := 64)
                                                                                                                                                                                                (← readReg vcsr)))))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if (((b__0 == (0x321#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                  (← readReg mcyclecfg)
                                                                                                                                                                                                  value))
                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                  (← readReg mcyclecfg))))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if (((b__0 == (0x321#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                      (← readReg mcyclecfg)
                                                                                                                                                                                                      ((Sail.BitVec.extractLsb
                                                                                                                                                                                                          (← readReg mcyclecfg)
                                                                                                                                                                                                          63
                                                                                                                                                                                                          32) +++ value)))
                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                        (← readReg mcyclecfg)
                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                        0))))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if (((b__0 == (0x721#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                          (← readReg mcyclecfg)
                                                                                                                                                                                                          (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                              (← readReg mcyclecfg)
                                                                                                                                                                                                              31
                                                                                                                                                                                                              0))))
                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                            (← readReg mcyclecfg)
                                                                                                                                                                                                            63
                                                                                                                                                                                                            32))))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if (((b__0 == (0x322#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                              (← readReg minstretcfg)
                                                                                                                                                                                                              value))
                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                (← readReg minstretcfg)
                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                0))))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if (((b__0 == (0x322#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                  (← readReg minstretcfg)
                                                                                                                                                                                                                  ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                      (← readReg minstretcfg)
                                                                                                                                                                                                                      63
                                                                                                                                                                                                                      32) +++ value)))
                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                    (← readReg minstretcfg)
                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                    0))))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if (((b__0 == (0x722#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                      (← readReg minstretcfg)
                                                                                                                                                                                                                      (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                          (← readReg minstretcfg)
                                                                                                                                                                                                                          31
                                                                                                                                                                                                                          0))))
                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                        (← readReg minstretcfg)
                                                                                                                                                                                                                        63
                                                                                                                                                                                                                        32))))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if (((b__0 == (0x30C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg mstateen0 (← (legalize_mstateen0
                                                                                                                                                                                                                          (← readReg mstateen0)
                                                                                                                                                                                                                          ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                              (← readReg mstateen0)
                                                                                                                                                                                                                              63
                                                                                                                                                                                                                              32) +++ value)))
                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                            (← readReg mstateen0)
                                                                                                                                                                                                                            31
                                                                                                                                                                                                                            0))))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if (((b__0 == (0x30D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg mstateen1 (legalize_mstateen1
                                                                                                                                                                                                                            (← readReg mstateen1)
                                                                                                                                                                                                                            ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                (← readReg mstateen1)
                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                32) +++ value))
                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                (← readReg mstateen1)
                                                                                                                                                                                                                                31
                                                                                                                                                                                                                                0))))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if (((b__0 == (0x30E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg mstateen2 (legalize_mstateen2
                                                                                                                                                                                                                                (← readReg mstateen2)
                                                                                                                                                                                                                                ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    (← readReg mstateen2)
                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                    32) +++ value))
                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    (← readReg mstateen2)
                                                                                                                                                                                                                                    31
                                                                                                                                                                                                                                    0))))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if (((b__0 == (0x30F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg mstateen3 (legalize_mstateen3
                                                                                                                                                                                                                                    (← readReg mstateen3)
                                                                                                                                                                                                                                    ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        (← readReg mstateen3)
                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                        32) +++ value))
                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        (← readReg mstateen3)
                                                                                                                                                                                                                                        31
                                                                                                                                                                                                                                        0))))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if (((b__0 == (0x30C#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg mstateen0 (← (legalize_mstateen0
                                                                                                                                                                                                                                          (← readReg mstateen0)
                                                                                                                                                                                                                                          value))
                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                          (← readReg mstateen0))))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if (((b__0 == (0x30D#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg mstateen1 (legalize_mstateen1
                                                                                                                                                                                                                                            (← readReg mstateen1)
                                                                                                                                                                                                                                            value)
                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                              (← readReg mstateen1))))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if (((b__0 == (0x30E#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg mstateen2 (legalize_mstateen2
                                                                                                                                                                                                                                                (← readReg mstateen2)
                                                                                                                                                                                                                                                value)
                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                  (← readReg mstateen2))))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if (((b__0 == (0x30F#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg mstateen3 (legalize_mstateen3
                                                                                                                                                                                                                                                    (← readReg mstateen3)
                                                                                                                                                                                                                                                    value)
                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                      (← readReg mstateen3))))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if (((b__0 == (0x31C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg mstateen0 (← (legalize_mstateen0
                                                                                                                                                                                                                                                          (← readReg mstateen0)
                                                                                                                                                                                                                                                          (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                              (← readReg mstateen0)
                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                              0))))
                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                            (← readReg mstateen0)
                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                            32))))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if (((b__0 == (0x31D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg mstateen1 (legalize_mstateen1
                                                                                                                                                                                                                                                            (← readReg mstateen1)
                                                                                                                                                                                                                                                            (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                (← readReg mstateen1)
                                                                                                                                                                                                                                                                31
                                                                                                                                                                                                                                                                0)))
                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                (← readReg mstateen1)
                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                32))))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if (((b__0 == (0x31E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg mstateen2 (legalize_mstateen2
                                                                                                                                                                                                                                                                (← readReg mstateen2)
                                                                                                                                                                                                                                                                (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    (← readReg mstateen2)
                                                                                                                                                                                                                                                                    31
                                                                                                                                                                                                                                                                    0)))
                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    (← readReg mstateen2)
                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                    32))))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if (((b__0 == (0x31F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg mstateen3 (legalize_mstateen3
                                                                                                                                                                                                                                                                    (← readReg mstateen3)
                                                                                                                                                                                                                                                                    (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        (← readReg mstateen3)
                                                                                                                                                                                                                                                                        31
                                                                                                                                                                                                                                                                        0)))
                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        (← readReg mstateen3)
                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                        32))))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if (((b__0 == (0x60C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg hstateen0 (← (legalize_hstateen0
                                                                                                                                                                                                                                                                          (← readReg hstateen0)
                                                                                                                                                                                                                                                                          ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                              (← readReg hstateen0)
                                                                                                                                                                                                                                                                              63
                                                                                                                                                                                                                                                                              32) +++ value)))
                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            (← readReg hstateen0)
                                                                                                                                                                                                                                                                            31
                                                                                                                                                                                                                                                                            0))))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if (((b__0 == (0x60D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg hstateen1 (← (legalize_hstateen1
                                                                                                                                                                                                                                                                              (← readReg hstateen1)
                                                                                                                                                                                                                                                                              ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                  (← readReg hstateen1)
                                                                                                                                                                                                                                                                                  63
                                                                                                                                                                                                                                                                                  32) +++ value)))
                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                (← readReg hstateen1)
                                                                                                                                                                                                                                                                                31
                                                                                                                                                                                                                                                                                0))))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if (((b__0 == (0x60E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg hstateen2 (← (legalize_hstateen2
                                                                                                                                                                                                                                                                                  (← readReg hstateen2)
                                                                                                                                                                                                                                                                                  ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                      (← readReg hstateen2)
                                                                                                                                                                                                                                                                                      63
                                                                                                                                                                                                                                                                                      32) +++ value)))
                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                    (← readReg hstateen2)
                                                                                                                                                                                                                                                                                    31
                                                                                                                                                                                                                                                                                    0))))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if (((b__0 == (0x60F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg hstateen3 (← (legalize_hstateen3
                                                                                                                                                                                                                                                                                      (← readReg hstateen3)
                                                                                                                                                                                                                                                                                      ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                          (← readReg hstateen3)
                                                                                                                                                                                                                                                                                          63
                                                                                                                                                                                                                                                                                          32) +++ value)))
                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                        (← readReg hstateen3)
                                                                                                                                                                                                                                                                                        31
                                                                                                                                                                                                                                                                                        0))))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if (((b__0 == (0x60C#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg hstateen0 (← (legalize_hstateen0
                                                                                                                                                                                                                                                                                          (← readReg hstateen0)
                                                                                                                                                                                                                                                                                          value))
                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                          (← readReg hstateen0))))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if (((b__0 == (0x60D#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg hstateen1 (← (legalize_hstateen1
                                                                                                                                                                                                                                                                                              (← readReg hstateen1)
                                                                                                                                                                                                                                                                                              value))
                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                              (← readReg hstateen1))))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if (((b__0 == (0x60E#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg hstateen2 (← (legalize_hstateen2
                                                                                                                                                                                                                                                                                                  (← readReg hstateen2)
                                                                                                                                                                                                                                                                                                  value))
                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                  (← readReg hstateen2))))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if (((b__0 == (0x60F#12 : (BitVec 12))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  writeReg hstateen3 (← (legalize_hstateen3
                                                                                                                                                                                                                                                                                                      (← readReg hstateen3)
                                                                                                                                                                                                                                                                                                      value))
                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                      (← readReg hstateen3))))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if (((b__0 == (0x61C#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      writeReg hstateen0 (← (legalize_hstateen0
                                                                                                                                                                                                                                                                                                          (← readReg hstateen0)
                                                                                                                                                                                                                                                                                                          (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                              (← readReg hstateen0)
                                                                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                                                                              0))))
                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                            (← readReg hstateen0)
                                                                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                                                                            32))))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if (((b__0 == (0x61D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          writeReg hstateen1 (← (legalize_hstateen1
                                                                                                                                                                                                                                                                                                              (← readReg hstateen1)
                                                                                                                                                                                                                                                                                                              (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                  (← readReg hstateen1)
                                                                                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                                                                                  0))))
                                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                (← readReg hstateen1)
                                                                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                                                                32))))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if (((b__0 == (0x61E#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              writeReg hstateen2 (← (legalize_hstateen2
                                                                                                                                                                                                                                                                                                                  (← readReg hstateen2)
                                                                                                                                                                                                                                                                                                                  (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                      (← readReg hstateen2)
                                                                                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                                                                                      0))))
                                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                    (← readReg hstateen2)
                                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                                    32))))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if (((b__0 == (0x61F#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  writeReg hstateen3 (← (legalize_hstateen3
                                                                                                                                                                                                                                                                                                                      (← readReg hstateen3)
                                                                                                                                                                                                                                                                                                                      (value +++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                          (← readReg hstateen3)
                                                                                                                                                                                                                                                                                                                          31
                                                                                                                                                                                                                                                                                                                          0))))
                                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                        (← readReg hstateen3)
                                                                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                                                                        32))))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x10C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      writeReg sstateen0 (← (legalize_sstateen0
                                                                                                                                                                                                                                                                                                                          (← readReg sstateen0)
                                                                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                            value
                                                                                                                                                                                                                                                                                                                            31
                                                                                                                                                                                                                                                                                                                            0)))
                                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                                          (zero_extend
                                                                                                                                                                                                                                                                                                                            (m := 64)
                                                                                                                                                                                                                                                                                                                            (← readReg sstateen0)))))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x10D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          writeReg sstateen1 (legalize_sstateen1
                                                                                                                                                                                                                                                                                                                            (← readReg sstateen1)
                                                                                                                                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                              value
                                                                                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                                                                                              0))
                                                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                                                              (zero_extend
                                                                                                                                                                                                                                                                                                                                (m := 64)
                                                                                                                                                                                                                                                                                                                                (← readReg sstateen1)))))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x10E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              writeReg sstateen2 (legalize_sstateen2
                                                                                                                                                                                                                                                                                                                                (← readReg sstateen2)
                                                                                                                                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                  value
                                                                                                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                                                                                                  0))
                                                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                                                  (zero_extend
                                                                                                                                                                                                                                                                                                                                    (m := 64)
                                                                                                                                                                                                                                                                                                                                    (← readReg sstateen2)))))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x10F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  writeReg sstateen3 (legalize_sstateen3
                                                                                                                                                                                                                                                                                                                                    (← readReg sstateen3)
                                                                                                                                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                      value
                                                                                                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                                                                                                      0))
                                                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                                                      (zero_extend
                                                                                                                                                                                                                                                                                                                                        (m := 64)
                                                                                                                                                                                                                                                                                                                                        (← readReg sstateen3)))))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x180#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      writeReg satp (← (legalize_satp
                                                                                                                                                                                                                                                                                                                                          (← (architecture
                                                                                                                                                                                                                                                                                                                                              Supervisor))
                                                                                                                                                                                                                                                                                                                                          (← readReg satp)
                                                                                                                                                                                                                                                                                                                                          value))
                                                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                                                          (← readReg satp))))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x015#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (pure (Ok
                                                                                                                                                                                                                                                                                                                                            (write_seed_csr
                                                                                                                                                                                                                                                                                                                                              ())))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                                                                                                   11
                                                                                                                                                                                                                                                                                                                                                   5) == (0b0011001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                                                                                                   4
                                                                                                                                                                                                                                                                                                                                                   0)
                                                                                                                                                                                                                                                                                                                                               ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                   index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                  b__0
                                                                                                                                                                                                                                                                                                                                                  4
                                                                                                                                                                                                                                                                                                                                                  0)
                                                                                                                                                                                                                                                                                                                                              let index ← do
                                                                                                                                                                                                                                                                                                                                                (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                                  index)
                                                                                                                                                                                                                                                                                                                                              (write_mhpmevent
                                                                                                                                                                                                                                                                                                                                                index
                                                                                                                                                                                                                                                                                                                                                value)
                                                                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                                                                  (← (read_mhpmevent
                                                                                                                                                                                                                                                                                                                                                      index)))))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                                       11
                                                                                                                                                                                                                                                                                                                                                       5) == (0b1011000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                                                                                                                                                   ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                       index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                      b__0
                                                                                                                                                                                                                                                                                                                                                      4
                                                                                                                                                                                                                                                                                                                                                      0)
                                                                                                                                                                                                                                                                                                                                                  let index ← do
                                                                                                                                                                                                                                                                                                                                                    (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                                      index)
                                                                                                                                                                                                                                                                                                                                                  (write_mhpmcounter
                                                                                                                                                                                                                                                                                                                                                    index
                                                                                                                                                                                                                                                                                                                                                    value)
                                                                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                                                                      (← (read_mhpmcounter
                                                                                                                                                                                                                                                                                                                                                          index)))))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                                                                                                                           5) == (0b1011100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                                                                                                                       ((xlen == 32) && (((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                             index) ≥b 3) : Bool)))) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                                                                                                                      let index ← do
                                                                                                                                                                                                                                                                                                                                                        (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                                          index)
                                                                                                                                                                                                                                                                                                                                                      (write_mhpmcounterh
                                                                                                                                                                                                                                                                                                                                                        index
                                                                                                                                                                                                                                                                                                                                                        value)
                                                                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                                                                          (← (read_mhpmcounterh
                                                                                                                                                                                                                                                                                                                                                              index)))))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                                                                                                                               5) == (0b0111001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                                                                                                                                           ((xlen == 32) && (((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                 index) ≥b 3) : Bool)))) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                              b__0
                                                                                                                                                                                                                                                                                                                                                              4
                                                                                                                                                                                                                                                                                                                                                              0)
                                                                                                                                                                                                                                                                                                                                                          let index ← do
                                                                                                                                                                                                                                                                                                                                                            (hpmidx_from_bits
                                                                                                                                                                                                                                                                                                                                                              index)
                                                                                                                                                                                                                                                                                                                                                          (write_mhpmeventh
                                                                                                                                                                                                                                                                                                                                                            index
                                                                                                                                                                                                                                                                                                                                                            value)
                                                                                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                                                                                              (← (read_mhpmeventh
                                                                                                                                                                                                                                                                                                                                                                  index)))))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x14D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              writeReg stimecmp (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                0
                                                                                                                                                                                                                                                                                                                                                                value)
                                                                                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                    (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                    0))))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if (((b__0 == (0x15D#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  writeReg stimecmp (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                    (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                                                                                    32
                                                                                                                                                                                                                                                                                                                                                                    value)
                                                                                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                        (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                                                                                                                        32))))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x011#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      writeReg ssp (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                        value
                                                                                                                                                                                                                                                                                                                                                                        2
                                                                                                                                                                                                                                                                                                                                                                        0
                                                                                                                                                                                                                                                                                                                                                                        0b000#3)
                                                                                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                          (← readReg ssp))))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xB00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          writeReg mcycle (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                            (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                            0
                                                                                                                                                                                                                                                                                                                                                                            value)
                                                                                                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                              value)))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xB02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              writeReg minstret (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                                (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                                                                                                                                0
                                                                                                                                                                                                                                                                                                                                                                                value)
                                                                                                                                                                                                                                                                                                                                                                              writeReg minstret_increment false
                                                                                                                                                                                                                                                                                                                                                                              (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                                  value)))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if (((b__0 == (0xB80#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  writeReg mcycle (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                                    (← readReg mcycle)
                                                                                                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                                                                                                    32
                                                                                                                                                                                                                                                                                                                                                                                    value)
                                                                                                                                                                                                                                                                                                                                                                                  (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                                      value)))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if (((b__0 == (0xB82#12 : (BitVec 12))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      writeReg minstret (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                                                                                                                                        (← readReg minstret)
                                                                                                                                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                                                                                                                                        32
                                                                                                                                                                                                                                                                                                                                                                                        value)
                                                                                                                                                                                                                                                                                                                                                                                      writeReg minstret_increment false
                                                                                                                                                                                                                                                                                                                                                                                      (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                                          value)))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x181#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                          writeReg srmcfg (legalize_srmcfg
                                                                                                                                                                                                                                                                                                                                                                                            (← readReg srmcfg)
                                                                                                                                                                                                                                                                                                                                                                                            value)
                                                                                                                                                                                                                                                                                                                                                                                          (pure (Ok
                                                                                                                                                                                                                                                                                                                                                                                              (← readReg srmcfg))))
                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                        (internal_error
                                                                                                                                                                                                                                                                                                                                                                                          "postlude/csr_end.sail"
                                                                                                                                                                                                                                                                                                                                                                                          23
                                                                                                                                                                                                                                                                                                                                                                                          (HAppend.hAppend
                                                                                                                                                                                                                                                                                                                                                                                            "Write to CSR that does not exist: "
                                                                                                                                                                                                                                                                                                                                                                                            (BitVec.toFormatted
                                                                                                                                                                                                                                                                                                                                                                                              b__0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def doCSR (csr : (BitVec 12)) (rs1_val : (BitVec 64)) (rd : regidx) (op : csrop) (access_type : CSRAccessType) : SailM ExecutionResult := do
  if ((not (← (check_CSR csr (← readReg cur_privilege) access_type))) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_CSR csr (← readReg cur_privilege) access_type)) : Bool)
      then (pure (Ext_CSR_Check_Failure ()))
      else
        (do
          let csr_val ← (( do
            if ((bne access_type CSRWrite) : Bool)
            then (read_CSR csr)
            else (pure (zeros (n := 64))) ) : SailM xlenbits )
          if ((bne access_type CSRRead) : Bool)
          then
            (do
              let new_val : xlenbits :=
                match op with
                | .CSRRW => rs1_val
                | .CSRRS => (csr_val ||| rs1_val)
                | .CSRRC => (csr_val &&& (Complement.complement rs1_val))
              match (← (write_CSR csr new_val)) with
              | .Ok final_val =>
                (do
                  (csr_id_write_callback csr final_val)
                  (wX_bits rd csr_val)
                  (pure RETIRE_SUCCESS))
              | .Err () => (pure (Illegal_Instruction ())))
          else
            (do
              (csr_id_read_callback csr csr_val)
              (wX_bits rd csr_val)
              (pure RETIRE_SUCCESS))))

def csr_mnemonic_backwards (arg_ : String) : SailM csrop := do
  match arg_ with
  | "csrrw" => (pure CSRRW)
  | "csrrs" => (pure CSRRS)
  | "csrrc" => (pure CSRRC)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_mnemonic_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | .CSRRW => true
  | .CSRRS => true
  | .CSRRC => true

def csr_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "csrrw" => true
  | "csrrs" => true
  | "csrrc" => true
  | _ => false

