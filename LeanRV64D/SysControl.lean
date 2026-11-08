import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.Xlen
import LeanRV64D.PlatformConfig
import LeanRV64D.Extensions
import LeanRV64D.Types
import LeanRV64D.Callbacks
import LeanRV64D.PcAccess
import LeanRV64D.SysRegs
import LeanRV64D.InterruptRegs
import LeanRV64D.SysExceptions
import LeanRV64D.PmpRegs
import LeanRV64D.PmpControl
import LeanRV64D.StateenRegs
import LeanRV64D.ZicfilpRegs
import LeanRV64D.StateenAccessChecks
import LeanRV64D.SysReservation

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
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

def effectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((bne access (InstructionFetch ())) && ((_get_Mstatus_MPRV m) == 1#1)) : Bool)
  then (privLevel_bits_forwards ((_get_Mstatus_MPP m), 0#1))
  else (pure priv)

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def privLevel_to_CSR_privbits (p : Privilege) : SailM (BitVec 2) := do
  match p with
  | .User => (pure 0b00#2)
  | .VirtualUser => (pure 0b00#2)
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure 0b10#2)
      else (pure 0b01#2))
  | .VirtualSupervisor => (pure 0b01#2)
  | .Machine => (pure 0b11#2)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (zopz0zKzJ_u (← (privLevel_to_CSR_privbits p)) (csrPriv csr)))

def check_CSR_access (csr : (BitVec 12)) (access_type : CSRAccessType) : Bool :=
  (not (((access_type == CSRWrite) || (access_type == CSRReadWrite)) && ((csrAccess csr) == 0b11#2)))

def is_ssp_accessible (priv : Privilege) : SailM Bool := do
  match priv with
  | .Machine => (pure true)
  | .Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg))))
  | .VirtualSupervisor =>
    (internal_error "extensions/cfi/zicfiss_regs.sail" 40 "Hypervisor extension not supported")
  | .VirtualUser =>
    (internal_error "extensions/cfi/zicfiss_regs.sail" 43 "Hypervisor extension not supported")
  | .User =>
    (currentlyEnabled Ext_S) <&&> (do
      (pure (bool_bit_backwards (_get_SEnvcfg_SSE (← (read_senvcfg ())))))) <||> (do
      (pure (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg)))))

def sstc_CSRs_accessible (priv : Privilege) : SailM Bool := do
  (pure (priv == Machine)) <||> (do
    (pure (priv == Supervisor)) <&&> (do
      (pure ((_get_Counteren_TM (← readReg mcounteren)) == 1#1)) <&&> (do
        (pure ((_get_MEnvcfg_STCE (← readReg menvcfg)) == 1#1)))))

def is_CSR_accessible (b__0 : (BitVec 12)) (g__2 : Privilege) (g__3 : CSRAccessType) : SailM Bool := do
  if ((b__0 == (0x301#12 : (BitVec 12))) : Bool)
  then (pure true)
  else
    (do
      if ((b__0 == (0x300#12 : (BitVec 12))) : Bool)
      then (pure true)
      else
        (do
          if ((b__0 == (0x310#12 : (BitVec 12))) : Bool)
          then (pure (xlen == 32))
          else
            (do
              if ((b__0 == (0x747#12 : (BitVec 12))) : Bool)
              then (pure ((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)))
              else
                (do
                  if ((b__0 == (0x757#12 : (BitVec 12))) : Bool)
                  then
                    (pure (((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)) && (xlen == 32)))
                  else
                    (do
                      if ((b__0 == (0x30A#12 : (BitVec 12))) : Bool)
                      then (currentlyEnabled Ext_U)
                      else
                        (do
                          if ((b__0 == (0x31A#12 : (BitVec 12))) : Bool)
                          then (pure ((← (currentlyEnabled Ext_U)) && (xlen == 32)))
                          else
                            (do
                              if ((b__0 == (0x10A#12 : (BitVec 12))) : Bool)
                              then (currentlyEnabled Ext_S)
                              else
                                (do
                                  if ((b__0 == (0x342#12 : (BitVec 12))) : Bool)
                                  then (pure true)
                                  else
                                    (do
                                      if ((b__0 == (0x343#12 : (BitVec 12))) : Bool)
                                      then (pure true)
                                      else
                                        (do
                                          if ((b__0 == (0x340#12 : (BitVec 12))) : Bool)
                                          then (pure true)
                                          else
                                            (do
                                              if ((b__0 == (0x106#12 : (BitVec 12))) : Bool)
                                              then (currentlyEnabled Ext_S)
                                              else
                                                (do
                                                  if ((b__0 == (0x306#12 : (BitVec 12))) : Bool)
                                                  then (currentlyEnabled Ext_U)
                                                  else
                                                    (do
                                                      if ((b__0 == (0x320#12 : (BitVec 12))) : Bool)
                                                      then (pure true)
                                                      else
                                                        (do
                                                          if ((b__0 == (0xF11#12 : (BitVec 12))) : Bool)
                                                          then (pure true)
                                                          else
                                                            (do
                                                              if ((b__0 == (0xF12#12 : (BitVec 12))) : Bool)
                                                              then (pure true)
                                                              else
                                                                (do
                                                                  if ((b__0 == (0xF13#12 : (BitVec 12))) : Bool)
                                                                  then (pure true)
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0xF14#12 : (BitVec 12))) : Bool)
                                                                      then (pure true)
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0xF15#12 : (BitVec 12))) : Bool)
                                                                          then (pure true)
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0x100#12 : (BitVec 12))) : Bool)
                                                                              then
                                                                                (currentlyEnabled
                                                                                  Ext_S)
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0x140#12 : (BitVec 12))) : Bool)
                                                                                  then
                                                                                    (currentlyEnabled
                                                                                      Ext_S)
                                                                                  else
                                                                                    (do
                                                                                      if ((b__0 == (0x142#12 : (BitVec 12))) : Bool)
                                                                                      then
                                                                                        (currentlyEnabled
                                                                                          Ext_S)
                                                                                      else
                                                                                        (do
                                                                                          if ((b__0 == (0x143#12 : (BitVec 12))) : Bool)
                                                                                          then
                                                                                            (currentlyEnabled
                                                                                              Ext_S)
                                                                                          else
                                                                                            (do
                                                                                              if ((b__0 == (0x7A0#12 : (BitVec 12))) : Bool)
                                                                                              then
                                                                                                (pure true)
                                                                                              else
                                                                                                (do
                                                                                                  if ((b__0 == (0x304#12 : (BitVec 12))) : Bool)
                                                                                                  then
                                                                                                    (pure true)
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((b__0 == (0x344#12 : (BitVec 12))) : Bool)
                                                                                                      then
                                                                                                        (pure true)
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((b__0 == (0x302#12 : (BitVec 12))) : Bool)
                                                                                                          then
                                                                                                            (currentlyEnabled
                                                                                                              Ext_S)
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((b__0 == (0x312#12 : (BitVec 12))) : Bool)
                                                                                                              then
                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                        Ext_S)) && (xlen == 32)))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0x303#12 : (BitVec 12))) : Bool)
                                                                                                                  then
                                                                                                                    (currentlyEnabled
                                                                                                                      Ext_S)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((b__0 == (0x144#12 : (BitVec 12))) : Bool)
                                                                                                                      then
                                                                                                                        (currentlyEnabled
                                                                                                                          Ext_S)
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((b__0 == (0x104#12 : (BitVec 12))) : Bool)
                                                                                                                          then
                                                                                                                            (currentlyEnabled
                                                                                                                              Ext_S)
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((b__0 == (0x105#12 : (BitVec 12))) : Bool)
                                                                                                                              then
                                                                                                                                (currentlyEnabled
                                                                                                                                  Ext_S)
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((b__0 == (0x141#12 : (BitVec 12))) : Bool)
                                                                                                                                  then
                                                                                                                                    (currentlyEnabled
                                                                                                                                      Ext_S)
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((b__0 == (0x305#12 : (BitVec 12))) : Bool)
                                                                                                                                      then
                                                                                                                                        (pure true)
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((b__0 == (0x341#12 : (BitVec 12))) : Bool)
                                                                                                                                          then
                                                                                                                                            (pure true)
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                     b__0
                                                                                                                                                     11
                                                                                                                                                     4) == (0x3A#8 : (BitVec 8))) : Bool)
                                                                                                                                              then
                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    b__0
                                                                                                                                                    3
                                                                                                                                                    0)
                                                                                                                                                (pure ((sys_pmp_count >b (4 *i (BitVec.toNatInt
                                                                                                                                                          idx))) && (((BitVec.access
                                                                                                                                                          idx
                                                                                                                                                          0) == 0#1) || (xlen == 32)))))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                                                                         b__0
                                                                                                                                                         11
                                                                                                                                                         4) == (0x3B#8 : (BitVec 8))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (let idx : (BitVec 4) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        b__0
                                                                                                                                                        3
                                                                                                                                                        0)
                                                                                                                                                    (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                          (0b00#2 +++ idx)))))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if (((Sail.BitVec.extractLsb
                                                                                                                                                             b__0
                                                                                                                                                             11
                                                                                                                                                             4) == (0x3C#8 : (BitVec 8))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (let idx : (BitVec 4) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            b__0
                                                                                                                                                            3
                                                                                                                                                            0)
                                                                                                                                                        (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                              (0b01#2 +++ idx)))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                                                                                 b__0
                                                                                                                                                                 11
                                                                                                                                                                 4) == (0x3D#8 : (BitVec 8))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (let idx : (BitVec 4) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                b__0
                                                                                                                                                                3
                                                                                                                                                                0)
                                                                                                                                                            (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                  (0b10#2 +++ idx)))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                                     b__0
                                                                                                                                                                     11
                                                                                                                                                                     4) == (0x3E#8 : (BitVec 8))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    b__0
                                                                                                                                                                    3
                                                                                                                                                                    0)
                                                                                                                                                                (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                      (0b11#2 +++ idx)))))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((b__0 == (0x001#12 : (BitVec 12))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                      Ext_F) <||> (do
                                                                                                                                                                      (currentlyEnabled
                                                                                                                                                                        Ext_Zfinx))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((b__0 == (0x002#12 : (BitVec 12))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                          Ext_F) <||> (do
                                                                                                                                                                          (currentlyEnabled
                                                                                                                                                                            Ext_Zfinx))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((b__0 == (0x003#12 : (BitVec 12))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                              Ext_F) <||> (do
                                                                                                                                                                              (currentlyEnabled
                                                                                                                                                                                Ext_Zfinx))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((b__0 == (0x008#12 : (BitVec 12))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                  Ext_Zve32x)
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((b__0 == (0x009#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                      Ext_Zve32x)
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((b__0 == (0x00A#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                          Ext_Zve32x)
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((b__0 == (0x00F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                              Ext_Zve32x)
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((b__0 == (0xC20#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                  Ext_Zve32x)
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((b__0 == (0xC21#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                      Ext_Zve32x)
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((b__0 == (0xC22#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                          Ext_Zve32x)
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((b__0 == (0x321#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                              Ext_Smcntrpmf)
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((b__0 == (0x721#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                        Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((b__0 == (0x322#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                      Ext_Smcntrpmf)
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((b__0 == (0x722#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((b__0 == (0x30C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (pure (is_mstateen_accessible
                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((b__0 == (0x30D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (pure (is_mstateen_accessible
                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((b__0 == (0x30E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (pure (is_mstateen_accessible
                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((b__0 == (0x30F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (pure (is_mstateen_accessible
                                                                                                                                                                                                                                            ()))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((b__0 == (0x31C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                  ()) && (xlen == 32)))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((b__0 == (0x31D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                      ()) && (xlen == 32)))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((b__0 == (0x31E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                          ()) && (xlen == 32)))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((b__0 == (0x31F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                              ()) && (xlen == 32)))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((b__0 == (0x60C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (is_hstateen_accessible
                                                                                                                                                                                                                                                              ())
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((b__0 == (0x60D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (is_hstateen_accessible
                                                                                                                                                                                                                                                                  ())
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((b__0 == (0x60E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (is_hstateen_accessible
                                                                                                                                                                                                                                                                      ())
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((b__0 == (0x60F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (is_hstateen_accessible
                                                                                                                                                                                                                                                                          ())
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((b__0 == (0x61C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                              (is_hstateen_accessible
                                                                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((b__0 == (0x61D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                  (is_hstateen_accessible
                                                                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((b__0 == (0x61E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                      (is_hstateen_accessible
                                                                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((b__0 == (0x61F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                          (is_hstateen_accessible
                                                                                                                                                                                                                                                                                            ()))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((b__0 == (0x10C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (is_sstateen_accessible
                                                                                                                                                                                                                                                                                              ())
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((b__0 == (0x10D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                  ())
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x10E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                      ())
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x10F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                          ())
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x180#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                              Ext_S) <&&> (do
                                                                                                                                                                                                                                                                                                              (pure (not
                                                                                                                                                                                                                                                                                                                  (←((pure (g__2 == Supervisor)) <&&> (do
                                                                                                                                                                                                                                                                                                                    (pure ((_get_Mstatus_TVM
                                                                                                                                                                                                                                                                                                                          (← readReg mstatus)) == 1#1))))))))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x015#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                  Ext_Zkr) <&&> (do
                                                                                                                                                                                                                                                                                                                  (pure (bne
                                                                                                                                                                                                                                                                                                                      g__3
                                                                                                                                                                                                                                                                                                                      CSRRead)) <&&> (do
                                                                                                                                                                                                                                                                                                                    match g__2 with
                                                                                                                                                                                                                                                                                                                    | .Machine =>
                                                                                                                                                                                                                                                                                                                      (pure true)
                                                                                                                                                                                                                                                                                                                    | .Supervisor =>
                                                                                                                                                                                                                                                                                                                      (pure ((_get_Seccfg_SSEED
                                                                                                                                                                                                                                                                                                                            (← readReg mseccfg)) == 1#1))
                                                                                                                                                                                                                                                                                                                    | .User =>
                                                                                                                                                                                                                                                                                                                      (pure ((_get_Seccfg_USEED
                                                                                                                                                                                                                                                                                                                            (← readReg mseccfg)) == 1#1))
                                                                                                                                                                                                                                                                                                                    | .VirtualSupervisor =>
                                                                                                                                                                                                                                                                                                                      (internal_error
                                                                                                                                                                                                                                                                                                                        "extensions/K/zkr_control.sail"
                                                                                                                                                                                                                                                                                                                        52
                                                                                                                                                                                                                                                                                                                        "Hypervisor extension not supported")
                                                                                                                                                                                                                                                                                                                    | .VirtualUser =>
                                                                                                                                                                                                                                                                                                                      (internal_error
                                                                                                                                                                                                                                                                                                                        "extensions/K/zkr_control.sail"
                                                                                                                                                                                                                                                                                                                        53
                                                                                                                                                                                                                                                                                                                        "Hypervisor extension not supported")))
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
                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                      Ext_Zihpm)
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
                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                          Ext_Zihpm)
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
                                                                                                                                                                                                                                                                                                                               ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                   index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                    Ext_Zihpm)) && (xlen == 32)))
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
                                                                                                                                                                                                                                                                                                                                  (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                    Ext_Zihpm) <&&> (do
                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                      Ext_U) <&&> (do
                                                                                                                                                                                                                                                                                                                                      (counter_enabled
                                                                                                                                                                                                                                                                                                                                        (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                          index)
                                                                                                                                                                                                                                                                                                                                        g__2))))
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
                                                                                                                                                                                                                                                                                                                                       ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                                                                                                      (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                        Ext_Zihpm) <&&> (do
                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                          Ext_U) <&&> (do
                                                                                                                                                                                                                                                                                                                                          (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                                                                            (counter_enabled
                                                                                                                                                                                                                                                                                                                                              (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                index)
                                                                                                                                                                                                                                                                                                                                              g__2)))))
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
                                                                                                                                                                                                                                                                                                                                           ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                               index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                Ext_Sscofpmf)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xDA0#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                              Ext_Sscofpmf) <&&> (do
                                                                                                                                                                                                                                                                                                                                              (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                Ext_S))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x14D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                  Ext_S) <&&> (do
                                                                                                                                                                                                                                                                                                                                                  (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                    Ext_Sstc) <&&> (do
                                                                                                                                                                                                                                                                                                                                                    (sstc_CSRs_accessible
                                                                                                                                                                                                                                                                                                                                                      g__2)))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x15D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                      Ext_S) <&&> (do
                                                                                                                                                                                                                                                                                                                                                      (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                        Ext_Sstc) <&&> (do
                                                                                                                                                                                                                                                                                                                                                        (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                                                                                          (sstc_CSRs_accessible
                                                                                                                                                                                                                                                                                                                                                            g__2))))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x011#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                          Ext_Zicfiss) <&&> (do
                                                                                                                                                                                                                                                                                                                                                          (is_ssp_accessible
                                                                                                                                                                                                                                                                                                                                                            (← readReg cur_privilege)))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xC00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                              Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                              (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                0
                                                                                                                                                                                                                                                                                                                                                                g__2))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xC01#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                  Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                  (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                    1
                                                                                                                                                                                                                                                                                                                                                                    g__2))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                      Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                      (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                        2
                                                                                                                                                                                                                                                                                                                                                                        g__2))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xC80#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                          Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                          (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                            (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                                                                                                              g__2)))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xC81#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                              Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                              (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                                (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                  1
                                                                                                                                                                                                                                                                                                                                                                                  g__2)))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xC82#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                  Ext_Zicntr) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                                  (pure (xlen == 32)) <&&> (do
                                                                                                                                                                                                                                                                                                                                                                                    (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                      2
                                                                                                                                                                                                                                                                                                                                                                                      g__2)))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xB00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                      Ext_Zicntr)
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xB02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                          Ext_Zicntr)
                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xB80#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Zicntr)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xB82#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                        Ext_Zicntr)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x181#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                      Ext_Ssqosid)
                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                    (pure false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def check_CSR (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM Bool := do
  (check_CSR_priv csr p) <&&> (do
    (pure (check_CSR_access csr access_type)) <&&> (do
      (is_CSR_accessible csr p access_type) <&&> (do
        (stateen_allows_CSR_access csr p access_type))))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (BitVec.toNatInt (exceptionType_bits_forwards e))
  let super ← do (pure (bit_to_bool (BitVec.access (← readReg medeleg) idx)))
  let deleg ← do
    if (((← (currentlyEnabled Ext_S)) && super) : Bool)
    then (pure Supervisor)
    else (pure Machine)
  if ((zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p)) : Bool)
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec 64)) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  if (((_get_Minterrupts_MEI ip) == 1#1) : Bool)
  then (some I_M_External)
  else
    (if (((_get_Minterrupts_MSI ip) == 1#1) : Bool)
    then (some I_M_Software)
    else
      (if (((_get_Minterrupts_MTI ip) == 1#1) : Bool)
      then (some I_M_Timer)
      else
        (if (((_get_Minterrupts_SEI ip) == 1#1) : Bool)
        then (some I_S_External)
        else
          (if (((_get_Minterrupts_SSI ip) == 1#1) : Bool)
          then (some I_S_Software)
          else
            (if (((_get_Minterrupts_STI ip) == 1#1) : Bool)
            then (some I_S_Timer)
            else
              (if (((_get_Minterrupts_LCOFI ip) == 1#1) : Bool)
              then (some I_COF)
              else none))))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec 64) × Privilege)) := do
  sail_assert (←((currentlyEnabled Ext_S) <||> (do
    (pure ((← readReg mideleg) == (zeros (n := 64))))))) "sys/sys_control.sail:91.58-91.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure ((←((pure (priv == Machine)) <&&> (do
          (pure ((_get_Mstatus_MIE (← readReg mstatus)) == 1#1))))) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure ((←((pure (priv == Supervisor)) <&&> (do
          (pure ((_get_Mstatus_SIE (← readReg mstatus)) == 1#1))))) || (priv == User)))
  if ((mIE && (pending_m != (zeros (n := 64)))) : Bool)
  then (pure (some (pending_m, Machine)))
  else
    (if ((sIE && (pending_s != (zeros (n := 64)))) : Bool)
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← readReg mip) &&& (← readReg mie)) != (zeros (n := 64))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec 64))) : (BitVec 64) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := 64))

def track_trap (p : Privilege) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  match p with
  | .Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | .Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | .User => (internal_error "sys/sys_control.sail" 169 "Invalid privilege level")
  | .VirtualUser => (internal_error "sys/sys_control.sail" 170 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "sys/sys_control.sail" 171 "Hypervisor extension not supported")

def trap_handler (del_priv : Privilege) (c : TrapCause) (pc : (BitVec 64)) (info : (Option (BitVec 64))) (ext : (Option Unit)) : SailM (BitVec 64) := do
  let is_interrupt := (trapCause_is_interrupt c)
  let cause := (trapCause_bits_forwards c)
  let _ : Unit := (trap_callback is_interrupt cause)
  if (((get_config_print_exception ()) || (get_config_print_interrupt ())) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend (trapCause_to_str c)
            (HAppend.hAppend " at priv "
              (HAppend.hAppend (← (privLevel_to_str del_priv))
                (HAppend.hAppend " with tval " (BitVec.toFormatted (tval info)))))))))
  else (pure ())
  if ((hartSupports Ext_Zicfilp) : Bool)
  then (zicfilp_preserve_elp_on_trap del_priv)
  else (pure ())
  match del_priv with
  | .Machine =>
    (do
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 1) (64 -i 1)
        (bool_to_bit is_interrupt))
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) cause))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
        (_get_Mstatus_MIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits (← readReg cur_privilege)))
      writeReg mtval (tval info)
      writeReg mepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg mcause)))
  | .Supervisor =>
    (do
      sail_assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 1) (64 -i 1)
        (bool_to_bit is_interrupt))
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) cause))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
        (_get_Mstatus_SIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
        (← do
          match (← readReg cur_privilege) with
          | .User => (pure 0#1)
          | .Supervisor => (pure 1#1)
          | .Machine =>
            (internal_error "sys/sys_control.sail" 220 "invalid privilege for s-mode trap")
          | .VirtualUser =>
            (internal_error "sys/sys_control.sail" 221 "Hypervisor extension not supported")
          | .VirtualSupervisor =>
            (internal_error "sys/sys_control.sail" 222 "Hypervisor extension not supported")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg scause)))
  | .User => (internal_error "sys/sys_control.sail" 235 "Invalid privilege level")
  | .VirtualUser => (internal_error "sys/sys_control.sail" 236 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "sys/sys_control.sail" 237 "Hypervisor extension not supported")

def exception_handler (cur_priv : Privilege) (ctl : ctl_result) (pc : (BitVec 64)) : SailM (BitVec 64) := do
  match ctl with
  | .CTL_TRAP e =>
    (do
      let del_priv ← do (exception_delegatee e.trap cur_priv)
      if ((get_config_print_exception ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "trapping from "
              (HAppend.hAppend (← (privLevel_to_str cur_priv))
                (HAppend.hAppend " to "
                  (HAppend.hAppend (← (privLevel_to_str del_priv))
                    (HAppend.hAppend " to handle " (exceptionType_to_str e.trap))))))))
      else (pure ())
      (trap_handler del_priv (Exception e.trap) pc e.excinfo e.ext))
  | .CTL_MRET () =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
        (_get_Mstatus_MPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 1#1)
      writeReg cur_privilege (← (privLevel_bits_forwards
          ((_get_Mstatus_MPP (← readReg mstatus)), 0#1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits
          (← do
            if ((← (currentlyEnabled Ext_U)) : Bool)
            then (pure User)
            else (pure Machine))))
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
      else (pure ())
      if ((hartSupports Ext_Zicfilp) : Bool)
      then (zicfilp_restore_elp_on_xret mRET (← readReg cur_privilege))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_exception ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (← (privLevel_to_str prev_priv))
                (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
      else (pure ())
      (prepare_xret_target Machine))
  | .CTL_SRET () =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 1#1)
      writeReg cur_privilege (← do
        if (((_get_Mstatus_SPP (← readReg mstatus)) == 1#1) : Bool)
        then (pure Supervisor)
        else (pure User))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 0#1)
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
      else (pure ())
      if ((hartSupports Ext_Zicfilp) : Bool)
      then (zicfilp_restore_elp_on_xret sRET (← readReg cur_privilege))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_exception ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (← (privLevel_to_str prev_priv))
                (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
      else (pure ())
      (prepare_xret_target Supervisor))

def xtval_exception_value (e : ExceptionType) (excinfo : (BitVec 64)) : (Option (BitVec 64)) :=
  if ((match e with
     | .E_Illegal_Instr () => illegal_instruction_writes_xtval
     | .E_Virtual_Instr () => virtual_instruction_writes_xtval
     | .E_Breakpoint .Brk_Software => software_breakpoint_writes_xtval
     | .E_Breakpoint .Brk_Hardware => hardware_breakpoint_writes_xtval
     | .E_Load_Addr_Align () => misaligned_load_writes_xtval
     | .E_Load_Access_Fault () => load_access_fault_writes_xtval
     | .E_Load_Page_Fault () => load_page_fault_writes_xtval
     | .E_Load_GPage_Fault () => load_guest_page_fault_writes_xtval
     | .E_SAMO_Addr_Align () => misaligned_samo_writes_xtval
     | .E_SAMO_Access_Fault () => samo_access_fault_writes_xtval
     | .E_SAMO_Page_Fault () => samo_page_fault_writes_xtval
     | .E_SAMO_GPage_Fault () => samo_guest_page_fault_writes_xtval
     | .E_Fetch_Addr_Align () => misaligned_fetch_writes_xtval
     | .E_Fetch_Access_Fault () => fetch_access_fault_writes_xtval
     | .E_Fetch_Page_Fault () => fetch_page_fault_writes_xtval
     | .E_Fetch_GPage_Fault () => fetch_guest_page_fault_writes_xtval
     | .E_Software_Check () => software_check_fault_writes_xtval
     | .E_U_EnvCall () => false
     | .E_S_EnvCall () => false
     | .E_VS_EnvCall () => false
     | .E_M_EnvCall () => false
     | .E_Extension _ => true
     | .E_Reserved_14 () => reserved_exceptions_write_xtval
     | .E_Reserved_16 () => reserved_exceptions_write_xtval
     | .E_Reserved_17 () => reserved_exceptions_write_xtval
     | .E_Reserved_19 () => reserved_exceptions_write_xtval) : Bool)
  then (some excinfo)
  else none

def make_sync_exception (e : ExceptionType) (xtval : (BitVec 64)) : sync_exception :=
  { trap := e
    excinfo := (xtval_exception_value e xtval)
    ext := none }

def handle_exception (xtval : (BitVec 64)) (e : ExceptionType) : SailM Unit := do
  let t := (make_sync_exception e xtval)
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc (← (trap_handler del_priv (Interrupt i) (← readReg PC) none none)))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bit (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bit (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bit (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bit (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bit (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bit (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bit (hartSupports Ext_V)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 4 4 (bool_to_bit base_E_enabled))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8
    (Complement.complement (_get_Misa_E (← readReg misa))))
  if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
  then (internal_error "sys/sys_control.sail" 354 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bit (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3 0#1)
  (csr_name_write_callback "misa" (← readReg misa))

def set_pc_reset_address (addr : (BitVec 64)) : SailM Unit := do
  writeReg pc_reset_address (trunc (m := 64) addr)

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg PC (← readReg pc_reset_address)
  writeReg nextPC (← readReg pc_reset_address)
  writeReg mcause (zeros (n := 64))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bit (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bit (false : Bool)))
  if ((hartSupports Ext_Zicfilp) : Bool)
  then writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 10 10 0#1)
  else (pure ())
  (reset_stateen ())
  writeReg vstart (zeros (n := 64))
  writeReg vl (zeros (n := 64))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 0b00#2)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 1) (64 -i 1) 1#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 2) 8
    (zeros (n := (64 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 0b000#3)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 0b000#3)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t ExceptionType)) (m : Unit) : (Result (k_t × Unit) ExceptionType) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) ExceptionType)) : (Result k_t ExceptionType) :=
  match r with
  | .Ok (v, _m) => (Ok v)
  | .Err e => (Err e)

