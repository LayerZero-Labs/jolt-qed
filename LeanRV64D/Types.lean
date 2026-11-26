import LeanRV64D.Flow
import LeanRV64D.Mapping
import LeanRV64D.HexBits
import LeanRV64D.HexBitsSigned
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.AextTypes
import LeanRV64D.Xlen
import LeanRV64D.Flen
import LeanRV64D.PlatformConfig
import LeanRV64D.Extensions
import LeanRV64D.TypesExt

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

noncomputable section
namespace LeanRV64D

open ConcurrencyInterfaceV1

namespace Functions

open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
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
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
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

def pagesize_bits := 12

def base_E_enabled := false

def regidx_bit_width := 5

def regidx_bits (app_0 : regidx) : (BitVec (if ( false  : Bool) then 4 else 5)) :=
  let .Regidx b := app_0
  b

def creg2reg_idx (app_0 : cregidx) : regidx :=
  let .Cregidx i := app_0
  (Regidx (zero_extend (m := 5) (1#1 +++ i)))

def zreg : regidx := (Regidx (zero_extend (m := 5) 0b00#2))

def ra : regidx := (Regidx (zero_extend (m := 5) 0b01#2))

def sp : regidx := (Regidx (zero_extend (m := 5) 0b10#2))

def t0 : regidx := (Regidx (zero_extend (m := 5) 0b101#3))

def undefined_Architecture (_ : Unit) : SailM Architecture := do
  (internal_pick [RV32, RV64, RV128])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Architecture_of_num (arg_ : Nat) : Architecture :=
  match arg_ with
  | 0 => RV32
  | 1 => RV64
  | _ => RV128

def num_of_Architecture (arg_ : Architecture) : Int :=
  match arg_ with
  | .RV32 => 0
  | .RV64 => 1
  | .RV128 => 2

def architecture_bits_forwards (arg_ : Architecture) : (BitVec 2) :=
  match arg_ with
  | .RV32 => 0b01#2
  | .RV64 => 0b10#2
  | .RV128 => 0b11#2

def architecture_bits_backwards (arg_ : (BitVec 2)) : SailM Architecture := do
  match arg_ with
  | 0b01 => (pure RV32)
  | 0b10 => (pure RV64)
  | 0b11 => (pure RV128)
  | _ => (internal_error "core/types.sail" 62 "architecture(0b00) is invalid")

def architecture_bits_forwards_matches (arg_ : Architecture) : Bool :=
  match arg_ with
  | .RV32 => true
  | .RV64 => true
  | .RV128 => true

def architecture_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | 0b00 => true
  | _ => false

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, VirtualUser, Supervisor, VirtualSupervisor, Machine])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Privilege_of_num (arg_ : Nat) : Privilege :=
  match arg_ with
  | 0 => User
  | 1 => VirtualUser
  | 2 => Supervisor
  | 3 => VirtualSupervisor
  | _ => Machine

def num_of_Privilege (arg_ : Privilege) : Int :=
  match arg_ with
  | .User => 0
  | .VirtualUser => 1
  | .Supervisor => 2
  | .VirtualSupervisor => 3
  | .Machine => 4

def privLevel_bits_forwards (arg_ : ((BitVec 2) × (BitVec 1))) : SailM Privilege := do
  match arg_ with
  | (0b00, 0) => (pure User)
  | (0b00, 1) => (pure VirtualUser)
  | (0b01, 0) => (pure Supervisor)
  | (0b01, 1) => (pure VirtualSupervisor)
  | (0b11, 0) => (pure Machine)
  | _ => (internal_error "core/types.sail" 79 "Invalid privilege level or virtual mode")

def privLevel_bits_backwards (arg_ : Privilege) : ((BitVec 2) × (BitVec 1)) :=
  match arg_ with
  | .User => (0b00#2, 0#1)
  | .VirtualUser => (0b00#2, 1#1)
  | .Supervisor => (0b01#2, 0#1)
  | .VirtualSupervisor => (0b01#2, 1#1)
  | .Machine => (0b11#2, 0#1)

def privLevel_bits_forwards_matches (arg_ : ((BitVec 2) × (BitVec 1))) : Bool :=
  match arg_ with
  | (0b00, 0) => true
  | (0b00, 1) => true
  | (0b01, 0) => true
  | (0b01, 1) => true
  | (0b11, 0) => true
  | _ => true

def privLevel_bits_backwards_matches (arg_ : Privilege) : Bool :=
  match arg_ with
  | .User => true
  | .VirtualUser => true
  | .Supervisor => true
  | .VirtualSupervisor => true
  | .Machine => true

def privLevel_to_bits (p : Privilege) : (BitVec 2) :=
  let (p, _) := (privLevel_bits_backwards p)
  p

def privLevel_to_virt_bit (p : Privilege) : (BitVec 1) :=
  let (_, v) := (privLevel_bits_backwards p)
  v

def privLevel_is_virtual (p : Privilege) : Bool :=
  ((p == VirtualSupervisor) || (p == VirtualUser))

def Mk_Misa (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Misa_MXL (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 2) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 2) x)

def Mk_Mstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Mstatus_MPP (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 11 x)

def _update_Mstatus_SXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_Mstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _get_Misa_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Misa_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Misa_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Misa_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_Misa_M (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_Misa_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_Misa_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_Misa_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_Mstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _get_Mstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def Mk_MEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_MEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_MEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_MEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_MEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_MEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_MEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_MEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_MEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_MEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_MEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def legalize_xenvcfg_cbie (cbie : (BitVec 2)) : SailM (BitVec 2) := do
  if ((cbie != 0b10#2) : Bool)
  then (pure cbie)
  else
    (do
      match xenvcfg_cbie_reserved_behavior with
      | .Xenvcfg_Fatal => (reserved_behavior "xenvcfg.CBIE = 0b10")
      | .Xenvcfg_ClearPermissions => (pure 0b00#2))

def sys_enable_writable_fiom : Bool := false

def Mk_Seccfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Seccfg_MLPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_Seccfg_SSEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_Seccfg_USEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Seccfg_MLPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_Seccfg_SSEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Seccfg_USEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_SEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def Mk_SEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_SEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def Mk_Hstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

def is_mstateen_accessible (_ : Unit) : Bool :=
  (hartSupports Ext_Smstateen)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_mstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (is_mstateen_accessible ())) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg mstateen0
      | 1 => readReg mstateen1
      | 2 => readReg mstateen2
      | _ => readReg mstateen3)

def Mk_Sstateen0 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen1 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen2 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen3 (v : (BitVec 32)) : (BitVec 32) :=
  v

def stateen_bit_index_forwards (arg_ : stateen_bit) : Nat :=
  match arg_ with
  | .STATEEN_SE => 63
  | .STATEEN_ENVCFG => 62
  | .STATEEN_SRMCFG => 55
  | .STATEEN_FCSR => 1

def read_senvcfg (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_SEnvcfg_SSE (← readReg senvcfg)
      ((_get_MEnvcfg_SSE (← readReg menvcfg)) &&& (_get_SEnvcfg_SSE (← readReg senvcfg)))))


mutual
/-- Type quantifiers: stateen_reg : Nat, 0 ≤ stateen_reg ∧ stateen_reg ≤ 3 -/
def check_stateen_bit (priv : Privilege) (bit_idx : stateen_bit) (stateen_reg : Nat) : SailM Bool := do
  let mask ← (( do
    match priv with
    | .Machine => (pure (ones (n := 64)))
    | .Supervisor => (get_mstateen stateen_reg)
    | .User => (pure ((← (get_mstateen stateen_reg)) &&& (← (get_sstateen stateen_reg))))
    | .VirtualSupervisor =>
      (pure ((← (get_mstateen stateen_reg)) &&& (← (get_hstateen stateen_reg))))
    | .VirtualUser =>
      (pure ((← (get_mstateen stateen_reg)) &&& ((← (get_hstateen stateen_reg)) &&& (← (get_sstateen
                stateen_reg))))) ) : SailM (BitVec 64) )
  (pure ((BitVec.access mask (stateen_bit_index_forwards bit_idx)) == 1#1))
termination_by (let (_, _, _) := (priv, bit_idx, stateen_reg)
7).toNat
def currentlyEnabled (merge_var : extension) : SailM Bool := do
  match merge_var with
  | .Ext_Zic64b => (pure (hartSupports Ext_Zic64b))
  | .Ext_Zkt => (pure (hartSupports Ext_Zkt))
  | .Ext_Zvkt => (pure (hartSupports Ext_Zvkt))
  | .Ext_Zvkn => (pure (hartSupports Ext_Zvkn))
  | .Ext_Zvknc => (pure (hartSupports Ext_Zvknc))
  | .Ext_Zvkng => (pure (hartSupports Ext_Zvkng))
  | .Ext_Zvks => (pure (hartSupports Ext_Zvks))
  | .Ext_Zvksc => (pure (hartSupports Ext_Zvksc))
  | .Ext_Zvksg => (pure (hartSupports Ext_Zvksg))
  | .Ext_Sstvala => (pure (hartSupports Ext_Sstvala)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | .Ext_U =>
    (pure (hartSupports Ext_U)) <&&> (do
      (pure ((_get_Misa_U (← readReg misa)) == 1#1)) <&&> (do
        (currentlyEnabled Ext_Zicsr)))
  | .Ext_S =>
    (pure (hartSupports Ext_S)) <&&> (do
      (pure ((_get_Misa_S (← readReg misa)) == 1#1)) <&&> (do
        (currentlyEnabled Ext_Zicsr)))
  | .Ext_Ssu64xl => (pure (hartSupports Ext_Ssu64xl)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Svbare => (currentlyEnabled Ext_S)
  | .Ext_Sv32 => (pure (hartSupports Ext_Sv32)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sv39 => (pure (hartSupports Ext_Sv39)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sv48 => (pure (hartSupports Ext_Sv48)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sv57 => (pure (hartSupports Ext_Sv57)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sstvecd => (pure (hartSupports Ext_Sstvecd)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Sscounterenw => (pure (hartSupports Ext_Sscounterenw)) <&&> (do (currentlyEnabled Ext_S))
  | .Ext_Smstateen => (pure (hartSupports Ext_Smstateen)) <&&> (do (currentlyEnabled Ext_Zicsr))
  | .Ext_Ssstateen => (pure (hartSupports Ext_Ssstateen)) <&&> (do (currentlyEnabled Ext_Zicsr))
  | .Ext_F =>
    (pure (hartSupports Ext_F)) <&&> (do
      (pure ((_get_Misa_F (← readReg misa)) == 1#1)) <&&> (do
        (pure ((_get_Mstatus_FS (← readReg mstatus)) != 0b00#2)) <&&> (do
          (currentlyEnabled Ext_Zicsr))))
  | .Ext_D =>
    (pure (hartSupports Ext_D)) <&&> (do
      (pure ((_get_Misa_D (← readReg misa)) == 1#1)) <&&> (do
        (pure ((_get_Mstatus_FS (← readReg mstatus)) != 0b00#2)) <&&> (do
          (pure (flen ≥b 64)) <&&> (do
            (currentlyEnabled Ext_Zicsr)))))
  | .Ext_Zfinx =>
    (pure (hartSupports Ext_Zfinx)) <&&> (do
      (currentlyEnabled Ext_Zicsr) <&&> (do
        (is_zfinx_enabled_by_stateen ())))
  | .Ext_Zvl32b => (pure (hartSupports Ext_Zvl32b))
  | .Ext_Zvl64b => (pure (hartSupports Ext_Zvl64b))
  | .Ext_Zvl128b => (pure (hartSupports Ext_Zvl128b))
  | .Ext_Zvl256b => (pure (hartSupports Ext_Zvl256b))
  | .Ext_Zvl512b => (pure (hartSupports Ext_Zvl512b))
  | .Ext_Zvl1024b => (pure (hartSupports Ext_Zvl1024b))
  | .Ext_Zve32x =>
    (pure (hartSupports Ext_Zve32x)) <&&> (do
      (currentlyEnabled Ext_Zvl32b) <&&> (do
        (pure ((_get_Mstatus_VS (← readReg mstatus)) != 0b00#2)) <&&> (do
          (currentlyEnabled Ext_Zicsr))))
  | .Ext_Zve32f =>
    (pure (hartSupports Ext_Zve32f)) <&&> (do
      (currentlyEnabled Ext_Zve32x) <&&> (do
        (currentlyEnabled Ext_F)))
  | .Ext_Zve64x =>
    (pure (hartSupports Ext_Zve64x)) <&&> (do
      (currentlyEnabled Ext_Zvl64b) <&&> (do
        (currentlyEnabled Ext_Zve32x)))
  | .Ext_Zve64f =>
    (pure (hartSupports Ext_Zve64f)) <&&> (do
      (currentlyEnabled Ext_Zve64x) <&&> (do
        (currentlyEnabled Ext_Zve32f)))
  | .Ext_Zve64d =>
    (pure (hartSupports Ext_Zve64d)) <&&> (do
      (currentlyEnabled Ext_Zve64f) <&&> (do
        (currentlyEnabled Ext_D)))
  | .Ext_V =>
    (pure (hartSupports Ext_V)) <&&> (do
      (pure ((_get_Misa_V (← readReg misa)) == 1#1)) <&&> (do
        (currentlyEnabled Ext_Zvl128b) <&&> (do
          (currentlyEnabled Ext_Zve64d))))
  | .Ext_Zvfh =>
    (pure (hartSupports Ext_Zvfh)) <&&> (do
      (currentlyEnabled Ext_Zve32f) <&&> (do
        (currentlyEnabled Ext_Zfhmin)))
  | .Ext_Zvfhmin =>
    (pure (hartSupports Ext_Zvfhmin)) <&&> (do
      (currentlyEnabled Ext_Zve32f)) <||> (do
      (currentlyEnabled Ext_Zvfh))
  | .Ext_Smcntrpmf => (pure (hartSupports Ext_Smcntrpmf)) <&&> (do (currentlyEnabled Ext_Zicntr))
  | .Ext_Zicfilp =>
    (currentlyEnabled Ext_Zicsr) <&&> (do
      (pure (hartSupports Ext_Zicfilp)) <&&> (do
        (get_xLPE (← readReg cur_privilege))))
  | .Ext_Svpbmt => (pure false)
  | .Ext_Svnapot => (pure (hartSupports Ext_Svnapot)) <&&> (do (currentlyEnabled Ext_Sv39))
  | .Ext_Svrsw60t59b => (pure (hartSupports Ext_Svrsw60t59b)) <&&> (do (currentlyEnabled Ext_Sv39))
  | .Ext_Svvptc =>
    (pure (hartSupports Ext_Svvptc)) <&&> (do
      (currentlyEnabled Ext_Sv32) <||> (do
        (currentlyEnabled Ext_Sv39)))
  | .Ext_Ssccptr =>
    (pure (hartSupports Ext_Ssccptr)) <&&> (do
      (currentlyEnabled Ext_Sv32) <||> (do
        (currentlyEnabled Ext_Sv39)))
  | .Ext_C => (pure (hartSupports Ext_C)) <&&> (do (pure ((_get_Misa_C (← readReg misa)) == 1#1)))
  | .Ext_Zca =>
    (pure (hartSupports Ext_Zca)) <&&> (do
      (pure ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | .Ext_A => (pure (hartSupports Ext_A)) <&&> (do (pure ((_get_Misa_A (← readReg misa)) == 1#1)))
  | .Ext_Zaamo => (pure (hartSupports Ext_Zaamo)) <||> (do (currentlyEnabled Ext_A))
  | .Ext_Zabha => (pure (hartSupports Ext_Zabha)) <&&> (do (currentlyEnabled Ext_Zaamo))
  | .Ext_Zacas => (pure (hartSupports Ext_Zacas)) <&&> (do (currentlyEnabled Ext_Zaamo))
  | .Ext_Ziccamoa => (pure (hartSupports Ext_Ziccamoa))
  | .Ext_Ziccamoc => (pure (hartSupports Ext_Ziccamoc))
  | .Ext_Zalrsc => (pure (hartSupports Ext_Zalrsc)) <||> (do (currentlyEnabled Ext_A))
  | .Ext_Za64rs => (pure (hartSupports Ext_Za64rs)) <&&> (do (currentlyEnabled Ext_Zalrsc))
  | .Ext_Za128rs => (pure (hartSupports Ext_Za128rs)) <&&> (do (currentlyEnabled Ext_Zalrsc))
  | .Ext_Ziccrse => (pure (hartSupports Ext_Ziccrse))
  | .Ext_M => (pure (hartSupports Ext_M)) <&&> (do (pure ((_get_Misa_M (← readReg misa)) == 1#1)))
  | .Ext_Zmmul => (pure (hartSupports Ext_Zmmul)) <||> (do (currentlyEnabled Ext_M))
  | .Ext_Zbb => (pure (hartSupports Ext_Zbb)) <||> (do (currentlyEnabled Ext_B))
  | .Ext_Zbkb => (pure (hartSupports Ext_Zbkb))
  | .Ext_Zicsr => (pure (hartSupports Ext_Zicsr))
  | _ =>
    (do
      sail_assert false "Pattern match failure at extensions/Zicsr/zicsr_insts.sail:12.0-12.69"
      throw Error.Exit)
termination_by (let ext := merge_var
(currentlyEnabled_measure ext)).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_hstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (← (is_hstateen_accessible ()))) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg hstateen0
      | 1 => readReg hstateen1
      | 2 => readReg hstateen2
      | _ => readReg hstateen3)
termination_by (let _ := idx
6).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_sstateen (idx : Nat) : SailM (BitVec 64) := do
  (pure (0xFFFFFFFF#32 +++ (← do
        if ((not (← (is_sstateen_accessible ()))) : Bool)
        then (pure (ones (n := (64 -i 32))))
        else
          (do
            match idx with
            | 0 => readReg sstateen0
            | 1 => readReg sstateen1
            | 2 => readReg sstateen2
            | _ => readReg sstateen3))))
termination_by (let _ := idx
3).toNat
def get_xLPE (p : Privilege) : SailM Bool := do
  match p with
  | .Machine => (pure (bool_bit_backwards (_get_Seccfg_MLPE (← readReg mseccfg))))
  | .Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg))))
  | .User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (bool_bit_backwards (_get_SEnvcfg_LPE (← (read_senvcfg ())))))
      else (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg)))))
  | .VirtualSupervisor =>
    (internal_error "extensions/cfi/zicfilp_regs.sail" 31 "Hypervisor extension not supported")
  | .VirtualUser =>
    (internal_error "extensions/cfi/zicfilp_regs.sail" 32 "Hypervisor extension not supported")
termination_by (let _ := p
2).toNat
def is_hstateen_accessible (_ : Unit) : SailM Bool := do
  (currentlyEnabled Ext_H) <&&> (do
    (currentlyEnabled Ext_Smstateen) <||> (do
      (currentlyEnabled Ext_Ssstateen)))
termination_by (let () := ()
5).toNat
def is_sstateen_accessible (_ : Unit) : SailM Bool := do
  (currentlyEnabled Ext_S) <&&> (do
    (currentlyEnabled Ext_Smstateen) <||> (do
      (currentlyEnabled Ext_Ssstateen)))
termination_by (let () := ()
2).toNat
def is_zfinx_enabled_by_stateen (_ : Unit) : SailM Bool := do
  (check_stateen_bit (← readReg cur_privilege) STATEEN_FCSR 0)
termination_by (let () := ()
8).toNat
end

def legalize_menvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_MEnvcfg v)
  (pure (_update_MEnvcfg_STCE
      (_update_MEnvcfg_CBIE
        (_update_MEnvcfg_CBCFE
          (_update_MEnvcfg_CBZE
            (_update_MEnvcfg_SSE
              (_update_MEnvcfg_LPE
                (_update_MEnvcfg_FIOM o
                  (if (sys_enable_writable_fiom : Bool)
                  then (_get_MEnvcfg_FIOM v)
                  else 0#1))
                (if ((hartSupports Ext_Zicfilp) : Bool)
                then (_get_MEnvcfg_LPE v)
                else 0#1))
              (if ((hartSupports Ext_Zicfiss) : Bool)
              then (_get_MEnvcfg_SSE v)
              else 0#1))
            (← do
              if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
              then (pure (_get_MEnvcfg_CBZE v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
            then (pure (_get_MEnvcfg_CBCFE v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
          then (legalize_xenvcfg_cbie (_get_MEnvcfg_CBIE v))
          else (pure 0b00#2)))
      (← do
        if ((← (currentlyEnabled Ext_Sstc)) : Bool)
        then (pure (_get_MEnvcfg_STCE v))
        else (pure 0#1))))

def legalize_mseccfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let sseed_read_only_zero ← do
    (pure (false : Bool)) <||> (do
      (pure (not (← (currentlyEnabled Ext_S)))) <||> (do
        (pure (not (← (currentlyEnabled Ext_Zkr))))))
  let useed_read_only_zero ← do
    (pure (false : Bool)) <||> (do
      (pure (not (← (currentlyEnabled Ext_U)))) <||> (do
        (pure (not (← (currentlyEnabled Ext_Zkr))))))
  let v := (Mk_Seccfg v)
  (pure (_update_Seccfg_USEED
      (_update_Seccfg_SSEED
        (_update_Seccfg_MLPE o
          (if ((hartSupports Ext_Zicfilp) : Bool)
          then (_get_Seccfg_MLPE v)
          else 0#1))
        (if (sseed_read_only_zero : Bool)
        then 0#1
        else (_get_Seccfg_SSEED v)))
      (if (useed_read_only_zero : Bool)
      then 0#1
      else (_get_Seccfg_USEED v))))

def legalize_senvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_SEnvcfg v)
  (pure (_update_SEnvcfg_CBIE
      (_update_SEnvcfg_CBCFE
        (_update_SEnvcfg_CBZE
          (_update_SEnvcfg_SSE
            (_update_SEnvcfg_LPE
              (_update_SEnvcfg_FIOM o
                (if (sys_enable_writable_fiom : Bool)
                then (_get_SEnvcfg_FIOM v)
                else 0#1))
              (if ((hartSupports Ext_Zicfilp) : Bool)
              then (_get_SEnvcfg_LPE v)
              else 0#1))
            (if ((hartSupports Ext_Zicfiss) : Bool)
            then (_get_SEnvcfg_SSE v)
            else 0#1))
          (← do
            if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
            then (pure (_get_SEnvcfg_CBZE v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
          then (pure (_get_SEnvcfg_CBCFE v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
        then (legalize_xenvcfg_cbie (_get_SEnvcfg_CBIE v))
        else (pure 0b00#2))))

def privLevel_to_str (p : Privilege) : SailM String := do
  match p with
  | .User => (pure "U")
  | .VirtualUser => (pure "VU")
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure "HS")
      else (pure "S"))
  | .VirtualSupervisor => (pure "VS")
  | .Machine => (pure "M")

def mem_payload_str_forwards (arg_ : mem_payload) : String :=
  match arg_ with
  | .Data => ""
  | .PageTableEntry => ""
  | .ShadowStack => ".ss"

def accessType_to_str (access : (MemoryAccessType mem_payload)) : String :=
  match access with
  | .Load p => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .LoadReserved p => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .Store p => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .StoreConditional p => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .Atomic (_, lp, sp) =>
    (HAppend.hAppend "R"
      (HAppend.hAppend (mem_payload_str_forwards lp)
        (HAppend.hAppend "W" (mem_payload_str_forwards sp))))
  | .InstructionFetch () => "X"
  | .CacheAccess _ => "C"

def atomic_support_str_backwards (arg_ : String) : SailM AtomicSupport := do
  match arg_ with
  | "AMONone" => (pure AMONone)
  | "AMOSwap" => (pure AMOSwap)
  | "AMOLogical" => (pure AMOLogical)
  | "AMOArithmetic" => (pure AMOArithmetic)
  | "AMOCASW" => (pure AMOCASW)
  | "AMOCASD" => (pure AMOCASD)
  | "AMOCASQ" => (pure AMOCASQ)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def atomic_support_str_forwards (arg_ : AtomicSupport) : String :=
  match arg_ with
  | .AMONone => "AMONone"
  | .AMOSwap => "AMOSwap"
  | .AMOLogical => "AMOLogical"
  | .AMOArithmetic => "AMOArithmetic"
  | .AMOCASW => "AMOCASW"
  | .AMOCASD => "AMOCASD"
  | .AMOCASQ => "AMOCASQ"

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match arg_ with
  | 0x301 => (pure "misa")
  | 0x300 => (pure "mstatus")
  | 0x310 => (pure "mstatush")
  | 0x747 => (pure "mseccfg")
  | 0x757 => (pure "mseccfgh")
  | 0x30A => (pure "menvcfg")
  | 0x31A => (pure "menvcfgh")
  | 0x10A => (pure "senvcfg")
  | 0x342 => (pure "mcause")
  | 0x343 => (pure "mtval")
  | 0x340 => (pure "mscratch")
  | 0x106 => (pure "scounteren")
  | 0x306 => (pure "mcounteren")
  | 0x320 => (pure "mcountinhibit")
  | 0xF11 => (pure "mvendorid")
  | 0xF12 => (pure "marchid")
  | 0xF13 => (pure "mimpid")
  | 0xF14 => (pure "mhartid")
  | 0xF15 => (pure "mconfigptr")
  | 0x100 => (pure "sstatus")
  | 0x140 => (pure "sscratch")
  | 0x142 => (pure "scause")
  | 0x143 => (pure "stval")
  | 0x7A0 => (pure "tselect")
  | 0x7A1 => (pure "tdata1")
  | 0x7A2 => (pure "tdata2")
  | 0x7A3 => (pure "tdata3")
  | 0x304 => (pure "mie")
  | 0x344 => (pure "mip")
  | 0x302 => (pure "medeleg")
  | 0x312 => (pure "medelegh")
  | 0x303 => (pure "mideleg")
  | 0x144 => (pure "sip")
  | 0x104 => (pure "sie")
  | 0x105 => (pure "stvec")
  | 0x141 => (pure "sepc")
  | 0x305 => (pure "mtvec")
  | 0x341 => (pure "mepc")
  | 0x3A0 => (pure "pmpcfg0")
  | 0x3A1 => (pure "pmpcfg1")
  | 0x3A2 => (pure "pmpcfg2")
  | 0x3A3 => (pure "pmpcfg3")
  | 0x3A4 => (pure "pmpcfg4")
  | 0x3A5 => (pure "pmpcfg5")
  | 0x3A6 => (pure "pmpcfg6")
  | 0x3A7 => (pure "pmpcfg7")
  | 0x3A8 => (pure "pmpcfg8")
  | 0x3A9 => (pure "pmpcfg9")
  | 0x3AA => (pure "pmpcfg10")
  | 0x3AB => (pure "pmpcfg11")
  | 0x3AC => (pure "pmpcfg12")
  | 0x3AD => (pure "pmpcfg13")
  | 0x3AE => (pure "pmpcfg14")
  | 0x3AF => (pure "pmpcfg15")
  | 0x3B0 => (pure "pmpaddr0")
  | 0x3B1 => (pure "pmpaddr1")
  | 0x3B2 => (pure "pmpaddr2")
  | 0x3B3 => (pure "pmpaddr3")
  | 0x3B4 => (pure "pmpaddr4")
  | 0x3B5 => (pure "pmpaddr5")
  | 0x3B6 => (pure "pmpaddr6")
  | 0x3B7 => (pure "pmpaddr7")
  | 0x3B8 => (pure "pmpaddr8")
  | 0x3B9 => (pure "pmpaddr9")
  | 0x3BA => (pure "pmpaddr10")
  | 0x3BB => (pure "pmpaddr11")
  | 0x3BC => (pure "pmpaddr12")
  | 0x3BD => (pure "pmpaddr13")
  | 0x3BE => (pure "pmpaddr14")
  | 0x3BF => (pure "pmpaddr15")
  | 0x3C0 => (pure "pmpaddr16")
  | 0x3C1 => (pure "pmpaddr17")
  | 0x3C2 => (pure "pmpaddr18")
  | 0x3C3 => (pure "pmpaddr19")
  | 0x3C4 => (pure "pmpaddr20")
  | 0x3C5 => (pure "pmpaddr21")
  | 0x3C6 => (pure "pmpaddr22")
  | 0x3C7 => (pure "pmpaddr23")
  | 0x3C8 => (pure "pmpaddr24")
  | 0x3C9 => (pure "pmpaddr25")
  | 0x3CA => (pure "pmpaddr26")
  | 0x3CB => (pure "pmpaddr27")
  | 0x3CC => (pure "pmpaddr28")
  | 0x3CD => (pure "pmpaddr29")
  | 0x3CE => (pure "pmpaddr30")
  | 0x3CF => (pure "pmpaddr31")
  | 0x3D0 => (pure "pmpaddr32")
  | 0x3D1 => (pure "pmpaddr33")
  | 0x3D2 => (pure "pmpaddr34")
  | 0x3D3 => (pure "pmpaddr35")
  | 0x3D4 => (pure "pmpaddr36")
  | 0x3D5 => (pure "pmpaddr37")
  | 0x3D6 => (pure "pmpaddr38")
  | 0x3D7 => (pure "pmpaddr39")
  | 0x3D8 => (pure "pmpaddr40")
  | 0x3D9 => (pure "pmpaddr41")
  | 0x3DA => (pure "pmpaddr42")
  | 0x3DB => (pure "pmpaddr43")
  | 0x3DC => (pure "pmpaddr44")
  | 0x3DD => (pure "pmpaddr45")
  | 0x3DE => (pure "pmpaddr46")
  | 0x3DF => (pure "pmpaddr47")
  | 0x3E0 => (pure "pmpaddr48")
  | 0x3E1 => (pure "pmpaddr49")
  | 0x3E2 => (pure "pmpaddr50")
  | 0x3E3 => (pure "pmpaddr51")
  | 0x3E4 => (pure "pmpaddr52")
  | 0x3E5 => (pure "pmpaddr53")
  | 0x3E6 => (pure "pmpaddr54")
  | 0x3E7 => (pure "pmpaddr55")
  | 0x3E8 => (pure "pmpaddr56")
  | 0x3E9 => (pure "pmpaddr57")
  | 0x3EA => (pure "pmpaddr58")
  | 0x3EB => (pure "pmpaddr59")
  | 0x3EC => (pure "pmpaddr60")
  | 0x3ED => (pure "pmpaddr61")
  | 0x3EE => (pure "pmpaddr62")
  | 0x3EF => (pure "pmpaddr63")
  | 0x001 => (pure "fflags")
  | 0x002 => (pure "frm")
  | 0x003 => (pure "fcsr")
  | 0x008 => (pure "vstart")
  | 0x009 => (pure "vxsat")
  | 0x00A => (pure "vxrm")
  | 0x00F => (pure "vcsr")
  | 0xC20 => (pure "vl")
  | 0xC21 => (pure "vtype")
  | 0xC22 => (pure "vlenb")
  | 0x321 => (pure "mcyclecfg")
  | 0x721 => (pure "mcyclecfgh")
  | 0x322 => (pure "minstretcfg")
  | 0x722 => (pure "minstretcfgh")
  | 0x30C => (pure "mstateen0")
  | 0x30D => (pure "mstateen1")
  | 0x30E => (pure "mstateen2")
  | 0x30F => (pure "mstateen3")
  | 0x31C => (pure "mstateen0h")
  | 0x31D => (pure "mstateen1h")
  | 0x31E => (pure "mstateen2h")
  | 0x31F => (pure "mstateen3h")
  | 0x60C => (pure "hstateen0")
  | 0x60D => (pure "hstateen1")
  | 0x60E => (pure "hstateen2")
  | 0x60F => (pure "hstateen3")
  | 0x61C => (pure "hstateen0h")
  | 0x61D => (pure "hstateen1h")
  | 0x61E => (pure "hstateen2h")
  | 0x61F => (pure "hstateen3h")
  | 0x10C => (pure "sstateen0")
  | 0x10D => (pure "sstateen1")
  | 0x10E => (pure "sstateen2")
  | 0x10F => (pure "sstateen3")
  | 0x180 => (pure "satp")
  | reg => (hex_bits_12_forwards reg)

def csr_name (csr : (BitVec 12)) : SailM String := do
  (csr_name_map_forwards csr)

def exceptionType_to_str (e : ExceptionType) : String :=
  match e with
  | .E_Fetch_Addr_Align () => "misaligned-fetch"
  | .E_Fetch_Access_Fault () => "fetch-access-fault"
  | .E_Illegal_Instr () => "illegal-instruction"
  | .E_Load_Addr_Align () => "misaligned-load"
  | .E_Load_Access_Fault () => "load-access-fault"
  | .E_SAMO_Addr_Align () => "misaligned-store/amo"
  | .E_SAMO_Access_Fault () => "store/amo-access-fault"
  | .E_U_EnvCall () => "u-call"
  | .E_S_EnvCall () => "s-call"
  | .E_VS_EnvCall () => "vs-call"
  | .E_M_EnvCall () => "m-call"
  | .E_Fetch_Page_Fault () => "fetch-page-fault"
  | .E_Load_Page_Fault () => "load-page-fault"
  | .E_Reserved_14 () => "reserved-1"
  | .E_SAMO_Page_Fault () => "store/amo-page-fault"
  | .E_Reserved_16 () => "reserved-2"
  | .E_Reserved_17 () => "reserved-3"
  | .E_Software_Check () => "software-check-fault"
  | .E_Reserved_19 () => "reserved-19"
  | .E_Fetch_GPage_Fault () => "fetch-guest-page-fault"
  | .E_Load_GPage_Fault () => "load-guest-page-fault"
  | .E_Virtual_Instr () => "virtual-instruction"
  | .E_SAMO_GPage_Fault () => "store/amo-guest-page-fault"
  | .E_Breakpoint .Brk_Software => "software-breakpoint"
  | .E_Breakpoint .Brk_Hardware => "hardware-breakpoint"
  | .E_Extension e => (ext_exc_type_to_str e)

def btype_mnemonic_forwards (arg_ : bop) : String :=
  match arg_ with
  | .BEQ => "beq"
  | .BNE => "bne"
  | .BLT => "blt"
  | .BGE => "bge"
  | .BLTU => "bltu"
  | .BGEU => "bgeu"

def encdec_reg_backwards (arg_ : (BitVec 5)) : SailM regidx := do
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then (pure (Regidx (Sail.BitVec.extractLsb r (regidx_bit_width -i 1) 0)))
  else
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

def reg_abi_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "zero"
  | 0b00001 => "ra"
  | 0b00010 => "sp"
  | 0b00011 => "gp"
  | 0b00100 => "tp"
  | 0b00101 => "t0"
  | 0b00110 => "t1"
  | 0b00111 => "t2"
  | 0b01000 => "s0"
  | 0b01000 => "fp"
  | 0b01001 => "s1"
  | 0b01010 => "a0"
  | 0b01011 => "a1"
  | 0b01100 => "a2"
  | 0b01101 => "a3"
  | 0b01110 => "a4"
  | 0b01111 => "a5"
  | 0b10000 => "a6"
  | 0b10001 => "a7"
  | 0b10010 => "s2"
  | 0b10011 => "s3"
  | 0b10100 => "s4"
  | 0b10101 => "s5"
  | 0b10110 => "s6"
  | 0b10111 => "s7"
  | 0b11000 => "s8"
  | 0b11001 => "s9"
  | 0b11010 => "s10"
  | 0b11011 => "s11"
  | 0b11100 => "t3"
  | 0b11101 => "t4"
  | 0b11110 => "t5"
  | _ => "t6"

def reg_arch_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "x0"
  | 0b00001 => "x1"
  | 0b00010 => "x2"
  | 0b00011 => "x3"
  | 0b00100 => "x4"
  | 0b00101 => "x5"
  | 0b00110 => "x6"
  | 0b00111 => "x7"
  | 0b01000 => "x8"
  | 0b01001 => "x9"
  | 0b01010 => "x10"
  | 0b01011 => "x11"
  | 0b01100 => "x12"
  | 0b01101 => "x13"
  | 0b01110 => "x14"
  | 0b01111 => "x15"
  | 0b10000 => "x16"
  | 0b10001 => "x17"
  | 0b10010 => "x18"
  | 0b10011 => "x19"
  | 0b10100 => "x20"
  | 0b10101 => "x21"
  | 0b10110 => "x22"
  | 0b10111 => "x23"
  | 0b11000 => "x24"
  | 0b11001 => "x25"
  | 0b11010 => "x26"
  | 0b11011 => "x27"
  | 0b11100 => "x28"
  | 0b11101 => "x29"
  | 0b11110 => "x30"
  | _ => "x31"

def reg_name_forwards (arg_ : regidx) : SailM String := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((encdec_reg_forwards_matches mapping0_) : Bool)
  then
    (let i := (encdec_reg_forwards mapping0_)
    if ((get_config_use_abi_names ()) : Bool)
    then (some (reg_abi_name_raw_forwards i))
    else none)
  else none) with
  | .some result => (pure result)
  | none =>
    (do
      match (let mapping1_ := head_exp_
      if ((encdec_reg_forwards_matches mapping1_) : Bool)
      then
        (let i := (encdec_reg_forwards mapping1_)
        if ((not (get_config_use_abi_names ())) : Bool)
        then (some (reg_arch_name_raw_forwards i))
        else none)
      else none) with
      | .some result => (pure result)
      | _ =>
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def creg_name_forwards (arg_ : cregidx) : SailM String := do
  match arg_ with
  | .Cregidx i => (reg_name_forwards (← (encdec_reg_backwards (0b01#2 +++ (i : (BitVec 3))))))

def csr_mnemonic_forwards (arg_ : csrop) : String :=
  match arg_ with
  | .CSRRW => "csrrw"
  | .CSRRS => "csrrs"
  | .CSRRC => "csrrc"

def bit_maybe_i_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "i"
  | _ => ""

def bit_maybe_o_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "o"
  | _ => ""

def bit_maybe_r_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "r"
  | _ => ""

def bit_maybe_w_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "w"
  | _ => ""

def fence_bits_forwards (arg_ : (BitVec 4)) : String :=
  let b__0 := arg_
  if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
  then "0"
  else
    (let i : (BitVec 1) := (Sail.BitVec.extractLsb b__0 3 3)
    let w : (BitVec 1) := (Sail.BitVec.extractLsb b__0 0 0)
    let r : (BitVec 1) := (Sail.BitVec.extractLsb b__0 1 1)
    let o : (BitVec 1) := (Sail.BitVec.extractLsb b__0 2 2)
    let i : (BitVec 1) := (Sail.BitVec.extractLsb b__0 3 3)
    (String.append (bit_maybe_i_forwards i)
      (String.append (bit_maybe_o_forwards o)
        (String.append (bit_maybe_r_forwards r) (String.append (bit_maybe_w_forwards w) "")))))

def itype_mnemonic_forwards (arg_ : iop) : String :=
  match arg_ with
  | .ADDI => "addi"
  | .SLTI => "slti"
  | .SLTIU => "sltiu"
  | .XORI => "xori"
  | .ORI => "ori"
  | .ANDI => "andi"

/-- Type quantifiers: k_ex196064_ : Bool -/
def maybe_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => "u"
  | false => ""

def mul_mnemonic_forwards (arg_ : mul_op) : SailM String := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mul")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mulh")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure "mulhsu")
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure "mulhu")
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtype_mnemonic_forwards (arg_ : rop) : String :=
  match arg_ with
  | .ADD => "add"
  | .SLT => "slt"
  | .SLTU => "sltu"
  | .AND => "and"
  | .OR => "or"
  | .XOR => "xor"
  | .SLL => "sll"
  | .SRL => "srl"
  | .SUB => "sub"
  | .SRA => "sra"

def rtypew_mnemonic_forwards (arg_ : ropw) : String :=
  match arg_ with
  | .ADDW => "addw"
  | .SUBW => "subw"
  | .SLLW => "sllw"
  | .SRLW => "srlw"
  | .SRAW => "sraw"

def shiftiop_mnemonic_forwards (arg_ : sop) : String :=
  match arg_ with
  | .SLLI => "slli"
  | .SRLI => "srli"
  | .SRAI => "srai"

def shiftiwop_mnemonic_forwards (arg_ : sopw) : String :=
  match arg_ with
  | .SLLIW => "slliw"
  | .SRLIW => "srliw"
  | .SRAIW => "sraiw"

def sp_reg_name_forwards (arg_ : Unit) : SailM String := do
  match arg_ with
  | () =>
    (do
      if ((get_config_use_abi_names ()) : Bool)
      then (pure "sp")
      else
        (do
          if ((not (get_config_use_abi_names ())) : Bool)
          then (pure "x2")
          else
            (do
              sail_assert false "Pattern match failure at unknown location"
              throw Error.Exit)))

def utype_mnemonic_forwards (arg_ : uop) : String :=
  match arg_ with
  | .LUI => "lui"
  | .AUIPC => "auipc"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_mnemonic_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | _ => "d"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_mnemonic_wide_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | 8 => "d"
  | _ => "q"

def zbb_extop_mnemonic_forwards (arg_ : extop_zbb) : String :=
  match arg_ with
  | .SEXTB => "sext.b"
  | .SEXTH => "sext.h"
  | .ZEXTH => "zext.h"

def zbb_rtype_mnemonic_forwards (arg_ : brop_zbb) : String :=
  match arg_ with
  | .ANDN => "andn"
  | .ORN => "orn"
  | .XNOR => "xnor"
  | .MAX => "max"
  | .MAXU => "maxu"
  | .MIN => "min"
  | .MINU => "minu"
  | .ROL => "rol"
  | .ROR => "ror"

def zbb_rtypew_mnemonic_forwards (arg_ : bropw_zbb) : String :=
  match arg_ with
  | .ROLW => "rolw"
  | .RORW => "rorw"

def assembly_forwards (arg_ : instruction) : SailM String := do
  match arg_ with
  | .LPAD lpl =>
    (pure (String.append "lpad"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_20_forwards lpl)) ""))))
  | .UTYPE (imm, rd, op) =>
    (pure (String.append (utype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_20_forwards imm)) ""))))))
  | .JAL (imm, rd) =>
    (pure (String.append "jal"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_21_forwards imm)) ""))))))
  | .JALR (imm, rs1, rd) =>
    (pure (String.append "jalr"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_12_forwards imm))
                (String.append "("
                  (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))
  | .BTYPE (imm, rs2, rs1, op) =>
    (pure (String.append (btype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure (String.append (itype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .SHIFTIOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (pure (String.append "l"
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_u_forwards is_unsigned)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm))
                    (String.append "("
                      (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))
  | .STORE (imm, rs2, rs1, width) =>
    (pure (String.append "s"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .ADDIW (imm, rs1, rd) =>
    (pure (String.append "addiw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .RTYPEW (rs2, rs1, rd, op) =>
    (pure (String.append (rtypew_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiwop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
  | .FENCE_TSO () => (pure "fence.tso")
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (do
      if (((rs == zreg) && (rd == zreg)) : Bool)
      then
        (pure (HAppend.hAppend "fence"
            (HAppend.hAppend (spc_forwards ())
              (HAppend.hAppend (fence_bits_forwards pred)
                (HAppend.hAppend (sep_forwards ()) (fence_bits_forwards succ))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ECALL () => (pure "ecall")
  | .MRET () => (pure "mret")
  | .SRET () => (pure "sret")
  | .EBREAK () => (pure "ebreak")
  | .WFI () => (pure "wfi")
  | .SFENCE_VMA (rs1, rs2) =>
    (pure (String.append "sfence.vma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .AMO (op, aq, rl, rs2, rs1, width, rd) =>
    (pure (String.append (amo_mnemonic_forwards op)
        (String.append "."
          (String.append (width_mnemonic_wide_forwards width)
            (String.append (maybe_aqrl_forwards (aq, rl))
              (String.append (spc_forwards ())
                (String.append (← (reg_name_forwards rd))
                  (String.append (sep_forwards ())
                    (String.append (← (reg_name_forwards rs2))
                      (String.append (sep_forwards ())
                        (String.append "("
                          (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))))
  | .LOADRES (aq, rl, rs1, width, rd) =>
    (pure (String.append "lr."
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_aqrl_forwards (aq, rl))
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append "("
                    (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))
  | .STORECON (aq, rl, rs2, rs1, width, rd) =>
    (pure (String.append "sc."
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_aqrl_forwards (aq, rl))
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (pure (String.append (← (mul_mnemonic_forwards mul_op))
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .MULW (rs2, rs1, rd) =>
    (pure (String.append "mulw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append "w"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append "w"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))))
  | .RORIW (shamt, rs1, rd) =>
    (pure (String.append "roriw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
  | .RORI (shamt, rs1, rd) =>
    (pure (String.append "rori"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBB_RTYPEW (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtypew_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBB_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBB_EXTOP (rs1, rd, op) =>
    (pure (String.append (zbb_extop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .REV8 (rs1, rd) =>
    (pure (String.append "rev8"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .ORCB (rs1, rd) =>
    (pure (String.append "orc.b"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CPOP (rs1, rd) =>
    (pure (String.append "cpop"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CPOPW (rs1, rd) =>
    (pure (String.append "cpopw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CLZ (rs1, rd) =>
    (pure (String.append "clz"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CLZW (rs1, rd) =>
    (pure (String.append "clzw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CTZ (rs1, rd) =>
    (pure (String.append "ctz"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CTZW (rs1, rd) =>
    (pure (String.append "ctzw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .C_NOP 0b000000 => (pure "c.nop")
  | .C_NOP imm =>
    (do
      if ((imm != (zeros (n := 6))) : Bool)
      then
        (pure (String.append "c.nop"
            (String.append (spc_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI4SPN (rdc, nzimm) =>
    (do
      if ((nzimm != 0b00000000#8) : Bool)
      then
        (pure (String.append "c.addi4spn"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rdc))
                (String.append (sep_forwards ())
                  (String.append (← (sp_reg_name_forwards ()))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_10_forwards ((nzimm : (BitVec 8)) +++ 0b00#2)))
                        ""))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (uimm, rsc, rdc) =>
    (pure (String.append "c.lw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_LD (uimm, rsc, rdc) =>
    (pure (String.append "c.ld"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_SW (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .C_SD (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sd"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .C_ADDI (imm, rsd) =>
    (do
      if ((bne rsd zreg) : Bool)
      then
        (pure (String.append "c.addi"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL imm =>
    (do
      if ((xlen == 32) : Bool)
      then
        (pure (String.append "c.jal"
            (String.append (spc_forwards ())
              (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) +++ 0#1))) ""))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDIW (imm, rsd) =>
    (pure (String.append "c.addiw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rsd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_LI (imm, rd) =>
    (pure (String.append "c.li"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_ADDI16SP imm =>
    (do
      if ((imm != 0b000000#6) : Bool)
      then
        (pure (String.append "c.addi16sp"
            (String.append (spc_forwards ())
              (String.append (← (sp_reg_name_forwards ()))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_10_forwards ((imm : (BitVec 6)) +++ 0x0#4)))
                    ""))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (imm, rd) =>
    (do
      if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
      then
        (pure (String.append "c.lui"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (shamt, rsd) =>
    (pure (String.append "c.srli"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_SRAI (shamt, rsd) =>
    (pure (String.append "c.srai"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_ANDI (imm, rsd) =>
    (pure (String.append "c.andi"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_SUB (rsd, rs2) =>
    (pure (String.append "c.sub"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_XOR (rsd, rs2) =>
    (pure (String.append "c.xor"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_OR (rsd, rs2) =>
    (pure (String.append "c.or"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_AND (rsd, rs2) =>
    (pure (String.append "c.and"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_SUBW (rsd, rs2) =>
    (pure (String.append "c.subw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_ADDW (rsd, rs2) =>
    (pure (String.append "c.addw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_J imm =>
    (pure (String.append "c.j"
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) +++ 0#1))) ""))))
  | .C_BEQZ (imm, rs) =>
    (pure (String.append "c.beqz"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) +++ 0#1))) ""))))))
  | .C_BNEZ (imm, rs) =>
    (pure (String.append "c.bnez"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) +++ 0#1))) ""))))))
  | .C_SLLI (shamt, rsd) =>
    (pure (String.append "c.slli"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_LWSP (uimm, rd) =>
    (do
      if ((bne rd zreg) : Bool)
      then
        (pure (String.append "c.lwsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) +++ 0b00#2)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && (xlen == 64)) : Bool)
      then
        (pure (String.append "c.ldsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (uimm, rs2) =>
    (pure (String.append "c.swsp"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_SDSP (uimm, rs2) =>
    (pure (String.append "c.sdsp"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_JR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jalr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.mv"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () => (pure "c.ebreak")
  | .C_ADD (rsd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.add"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append "i"
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (csr_name_map_forwards csr))
                  (String.append (sep_forwards ())
                    (String.append (← (hex_bits_5_forwards imm)) "")))))))))
  | .CSRReg (csr, rs1, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (csr_name_map_forwards csr))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))))
  | .ILLEGAL s =>
    (pure (String.append "illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_32_forwards s)) ""))))
  | .C_ILLEGAL s =>
    (pure (String.append "c.illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_16_forwards s)) ""))))
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def assembly_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .LPAD lpl => true
  | .UTYPE (imm, rd, op) => true
  | .JAL (imm, rd) => true
  | .JALR (imm, rs1, rd) => true
  | .BTYPE (imm, rs2, rs1, op) => true
  | .ITYPE (imm, rs1, rd, op) => true
  | .SHIFTIOP (shamt, rs1, rd, op) => true
  | .RTYPE (rs2, rs1, rd, op) => true
  | .LOAD (imm, rs1, rd, is_unsigned, width) => true
  | .STORE (imm, rs2, rs1, width) => true
  | .ADDIW (imm, rs1, rd) => true
  | .RTYPEW (rs2, rs1, rd, op) => true
  | .SHIFTIWOP (shamt, rs1, rd, op) => true
  | .FENCE_TSO () => true
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (if (((rs == zreg) && (rd == zreg)) : Bool)
    then true
    else false)
  | .ECALL () => true
  | .MRET () => true
  | .SRET () => true
  | .EBREAK () => true
  | .WFI () => true
  | .SFENCE_VMA (rs1, rs2) => true
  | .AMO (op, aq, rl, rs2, rs1, width, rd) => true
  | .LOADRES (aq, rl, rs1, width, rd) => true
  | .STORECON (aq, rl, rs2, rs1, width, rd) => true
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .MULW (rs2, rs1, rd) => true
  | .DIVW (rs2, rs1, rd, is_unsigned) => true
  | .REMW (rs2, rs1, rd, is_unsigned) => true
  | .RORIW (shamt, rs1, rd) => true
  | .RORI (shamt, rs1, rd) => true
  | .ZBB_RTYPEW (rs2, rs1, rd, op) => true
  | .ZBB_RTYPE (rs2, rs1, rd, op) => true
  | .ZBB_EXTOP (rs1, rd, op) => true
  | .REV8 (rs1, rd) => true
  | .ORCB (rs1, rd) => true
  | .CPOP (rs1, rd) => true
  | .CPOPW (rs1, rd) => true
  | .CLZ (rs1, rd) => true
  | .CLZW (rs1, rd) => true
  | .CTZ (rs1, rd) => true
  | .CTZW (rs1, rd) => true
  | .C_NOP 0b000000 => true
  | .C_NOP imm =>
    (if ((imm != (zeros (n := 6))) : Bool)
    then true
    else false)
  | .C_ADDI4SPN (rdc, nzimm) =>
    (if ((nzimm != 0b00000000#8) : Bool)
    then true
    else false)
  | .C_LW (uimm, rsc, rdc) => true
  | .C_LD (uimm, rsc, rdc) => true
  | .C_SW (uimm, rsc1, rsc2) => true
  | .C_SD (uimm, rsc1, rsc2) => true
  | .C_ADDI (imm, rsd) =>
    (if ((bne rsd zreg) : Bool)
    then true
    else false)
  | .C_JAL imm =>
    (if ((xlen == 32) : Bool)
    then true
    else false)
  | .C_ADDIW (imm, rsd) => true
  | .C_LI (imm, rd) => true
  | .C_ADDI16SP imm =>
    (if ((imm != 0b000000#6) : Bool)
    then true
    else false)
  | .C_LUI (imm, rd) =>
    (if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
    then true
    else false)
  | .C_SRLI (shamt, rsd) => true
  | .C_SRAI (shamt, rsd) => true
  | .C_ANDI (imm, rsd) => true
  | .C_SUB (rsd, rs2) => true
  | .C_XOR (rsd, rs2) => true
  | .C_OR (rsd, rs2) => true
  | .C_AND (rsd, rs2) => true
  | .C_SUBW (rsd, rs2) => true
  | .C_ADDW (rsd, rs2) => true
  | .C_J imm => true
  | .C_BEQZ (imm, rs) => true
  | .C_BNEZ (imm, rs) => true
  | .C_SLLI (shamt, rsd) => true
  | .C_LWSP (uimm, rd) =>
    (if ((bne rd zreg) : Bool)
    then true
    else false)
  | .C_LDSP (uimm, rd) =>
    (if (((bne rd zreg) && (xlen == 64)) : Bool)
    then true
    else false)
  | .C_SWSP (uimm, rs2) => true
  | .C_SDSP (uimm, rs2) => true
  | .C_JR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_JALR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_MV (rd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .C_EBREAK () => true
  | .C_ADD (rsd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .CSRImm (csr, imm, rd, op) => true
  | .CSRReg (csr, rs1, rd, op) => true
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true
  | _ => false

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8, 16] -/
def amo_encoding_valid (width : Nat) (op : amoop) (typ_2 : regidx) (typ_3 : regidx) : SailM Bool := do
  let .Regidx rs2 : regidx := typ_2
  let .Regidx rd : regidx := typ_3
  (do
    if ((op == AMOCAS) : Bool)
    then (currentlyEnabled Ext_Zacas)
    else (currentlyEnabled Ext_Zaamo)) <&&> (do
    if ((width <b 4) : Bool)
    then (currentlyEnabled Ext_Zabha)
    else
      (pure (width ≤b xlen_bytes)) <||> (do
        (pure ((op == AMOCAS) && (width ≤b (xlen_bytes *i 2)))) <&&> (do
          if ((((BitVec.access rs2 0) == 1#1) || ((BitVec.access rd 0) == 1#1)) : Bool)
          then
            (do
              match amocas_odd_register_reserved_behavior with
              | .AMOCAS_Fatal =>
                (reserved_behavior
                  (HAppend.hAppend "AMOCAS.D/Q used an odd-numbered register (rs2 = "
                    (HAppend.hAppend (Int.repr (BitVec.toNatInt rs2))
                      (HAppend.hAppend ", rd = "
                        (HAppend.hAppend (Int.repr (BitVec.toNatInt rd)) ").")))))
              | .AMOCAS_Illegal => (pure false))
          else (pure true))))

def encdec_amoop_forwards (arg_ : amoop) : (BitVec 5) :=
  match arg_ with
  | .AMOSWAP => 0b00001#5
  | .AMOADD => 0b00000#5
  | .AMOXOR => 0b00100#5
  | .AMOAND => 0b01100#5
  | .AMOOR => 0b01000#5
  | .AMOMIN => 0b10000#5
  | .AMOMAX => 0b10100#5
  | .AMOMINU => 0b11000#5
  | .AMOMAXU => 0b11100#5
  | .AMOCAS => 0b00101#5

def encdec_bop_forwards (arg_ : bop) : (BitVec 3) :=
  match arg_ with
  | .BEQ => 0b000#3
  | .BNE => 0b001#3
  | .BLT => 0b100#3
  | .BGE => 0b101#3
  | .BLTU => 0b110#3
  | .BGEU => 0b111#3

def encdec_csrop_forwards (arg_ : csrop) : (BitVec 2) :=
  match arg_ with
  | .CSRRW => 0b01#2
  | .CSRRS => 0b10#2
  | .CSRRC => 0b11#2

def encdec_iop_forwards (arg_ : iop) : (BitVec 3) :=
  match arg_ with
  | .ADDI => 0b000#3
  | .SLTI => 0b010#3
  | .SLTIU => 0b011#3
  | .ANDI => 0b111#3
  | .ORI => 0b110#3
  | .XORI => 0b100#3

def encdec_mul_op_forwards (arg_ : mul_op) : SailM (BitVec 3) := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b000#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b001#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure 0b010#3)
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure 0b011#3)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_uop_forwards (arg_ : uop) : (BitVec 7) :=
  match arg_ with
  | .LUI => 0b0110111#7
  | .AUIPC => 0b0010111#7

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8] -/
def lrsc_width_valid (width : Nat) : Bool :=
  match width with
  | 4 => true
  | 8 => (xlen ≥b 64)
  | _ => false

/-- Type quantifiers: k_ex196149_ : Bool, width : Nat, List.elem width [1, 2, 4, 8] -/
def valid_load_encdec (width : Nat) (is_unsigned : Bool) : Bool :=
  ((width <b xlen_bytes) || ((not is_unsigned) && (width ≤b xlen_bytes)))

def virtual_memory_supported (_ : Unit) : SailM Bool := do
  (currentlyEnabled Ext_Sv32) <||> (do
    (currentlyEnabled Ext_Sv39) <||> (do
      (currentlyEnabled Ext_Sv48) <||> (do
        (currentlyEnabled Ext_Sv57))))

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_enc_forwards (arg_ : Nat) : (BitVec 2) :=
  match arg_ with
  | 1 => 0b00#2
  | 2 => 0b01#2
  | 4 => 0b10#2
  | _ => 0b11#2

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_enc_wide_forwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => 0b000#3
  | 2 => 0b001#3
  | 4 => 0b010#3
  | 8 => 0b011#3
  | _ => 0b100#3

noncomputable def encdec_forwards (arg_ : instruction) : SailM (BitVec 32) := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure ((lpl : (BitVec 20)) +++ (0b00000#5 +++ 0b0010111#7)))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .UTYPE (imm, rd, op) =>
    (pure ((imm : (BitVec 20)) +++ ((encdec_reg_forwards rd) +++ (encdec_uop_forwards op))))
  | .JAL (v__10, rd) =>
    (do
      if (((Sail.BitVec.extractLsb v__10 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__10 20 1)
        let imm := (Sail.BitVec.extractLsb v__10 20 1)
        (pure ((Sail.BitVec.extractLsb imm 19 19) +++ ((Sail.BitVec.extractLsb imm 9 0) +++ ((Sail.BitVec.extractLsb
                  imm 10 10) +++ ((Sail.BitVec.extractLsb imm 18 11) +++ ((encdec_reg_forwards rd) +++ 0b1101111#7)))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                rd) +++ 0b1100111#7)))))
  | .BTYPE (v__12, rs2, rs1, op) =>
    (do
      if (((Sail.BitVec.extractLsb v__12 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__12 12 1)
        let imm := (Sail.BitVec.extractLsb v__12 12 1)
        (pure ((Sail.BitVec.extractLsb imm 11 11) +++ ((Sail.BitVec.extractLsb imm 9 4) +++ ((encdec_reg_forwards
                  rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_bop_forwards op) +++ ((Sail.BitVec.extractLsb
                        imm 3 0) +++ ((Sail.BitVec.extractLsb imm 10 10) +++ 0b1100011#7)))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((encdec_iop_forwards op) +++ ((encdec_reg_forwards
                rd) +++ 0b0010011#7)))))
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) =>
    (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) =>
    (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) =>
    (pure (0b010000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0010011#7))))))
  | .RTYPE (rs2, rs1, rd, .ADD) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLT) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLTU) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b011#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .AND) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .OR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .XOR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SUB) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRA) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (do
      if ((valid_load_encdec width is_unsigned) : Bool)
      then
        (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((bool_bit_forwards
                  is_unsigned) +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards rd) +++ 0b0000011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE (imm, rs2, rs1, width) =>
    (pure ((Sail.BitVec.extractLsb imm 11 5) +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
              rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((Sail.BitVec.extractLsb imm 4 0) +++ 0b0100011#7)))))))
  | .ADDIW (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                rd) +++ 0b0011011#7)))))
  | .RTYPEW (rs2, rs1, rd, .ADDW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SUBW) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SLLW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SRLW) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .RTYPEW (rs2, rs1, rd, .SRAW) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0111011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) =>
    (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) =>
    (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) =>
    (pure (0b0100000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0011011#7))))))
  | .FENCE_TSO () =>
    (pure (0b1000#4 +++ (0b0011#4 +++ (0b0011#4 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b0001111#7)))))))
  | .FENCE (fm, pred, succ, rs, rd) =>
    (pure ((fm : (BitVec 4)) +++ ((pred : (BitVec 4)) +++ ((succ : (BitVec 4)) +++ ((encdec_reg_forwards
                rs) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0001111#7)))))))
  | .ECALL () =>
    (pure (0b000000000000#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .MRET () =>
    (pure (0b0011000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .SRET () =>
    (pure (0b0001000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .EBREAK () =>
    (pure (0b000000000001#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .WFI () =>
    (pure (0b000100000101#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then
        (pure (0b0001001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AMO (op, aq, rl, rs2, rs1, size, rd) =>
    (do
      if ((← (amo_encoding_valid size op rs2 rd)) : Bool)
      then
        (pure ((encdec_amoop_forwards op) +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ ((encdec_reg_forwards
                    rs2) +++ ((encdec_reg_forwards rs1) +++ ((width_enc_wide_forwards size) +++ ((encdec_reg_forwards
                          rd) +++ 0b0101111#7))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .LOADRES (aq, rl, rs1, width, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zalrsc)) && (lrsc_width_valid width)) : Bool)
      then
        (pure (0b00010#5 +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ (0b00000#5 +++ ((encdec_reg_forwards
                      rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards rd) +++ 0b0101111#7)))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORECON (aq, rl, rs2, rs1, width, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zalrsc)) && (lrsc_width_valid width)) : Bool)
      then
        (pure (0b00011#5 +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ ((encdec_reg_forwards
                    rs2) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards
                            rd) +++ 0b0101111#7)))))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if ((←((currentlyEnabled Ext_M) <||> (do
           (currentlyEnabled Ext_Zmmul)))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((← (encdec_mul_op_forwards
                      mul_op)) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MULW (rs2, rs1, rd) =>
    (do
      if ((←((pure (xlen == 64)) <&&> (do
           (currentlyEnabled Ext_M) <||> (do
             (currentlyEnabled Ext_Zmmul))))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((←((pure (xlen == 64)) <&&> (do
           (currentlyEnabled Ext_M)))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((←((pure (xlen == 64)) <&&> (do
           (currentlyEnabled Ext_M)))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RORIW (shamt, rs1, rd) =>
    (do
      if (((←((currentlyEnabled Ext_Zbb) <||> (do
             (currentlyEnabled Ext_Zbkb)))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RORI (shamt, rs1, rd) =>
    (do
      if (((←((currentlyEnabled Ext_Zbb) <||> (do
             (currentlyEnabled Ext_Zbkb)))) && ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))) : Bool)
      then
        (pure (0b011000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPEW (rs2, rs1, rd, .ROLW) =>
    (do
      if (((←((currentlyEnabled Ext_Zbb) <||> (do
             (currentlyEnabled Ext_Zbkb)))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPEW (rs2, rs1, rd, .RORW) =>
    (do
      if (((←((currentlyEnabled Ext_Zbb) <||> (do
             (currentlyEnabled Ext_Zbkb)))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ANDN) =>
    (do
      if ((←((currentlyEnabled Ext_Zbb) <||> (do
           (currentlyEnabled Ext_Zbkb)))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ORN) =>
    (do
      if ((←((currentlyEnabled Ext_Zbb) <||> (do
           (currentlyEnabled Ext_Zbkb)))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .XNOR) =>
    (do
      if ((←((currentlyEnabled Ext_Zbb) <||> (do
           (currentlyEnabled Ext_Zbkb)))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MAX) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MAXU) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MIN) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MINU) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ROL) =>
    (do
      if ((←((currentlyEnabled Ext_Zbb) <||> (do
           (currentlyEnabled Ext_Zbkb)))) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ROR) =>
    (do
      if ((←((currentlyEnabled Ext_Zbb) <||> (do
           (currentlyEnabled Ext_Zbkb)))) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .SEXTB) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00100#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .SEXTH) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00101#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .ZEXTH) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 32)) : Bool)
      then
        (pure (0b0000100#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
          then
            (pure (0b0000100#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                          rd) +++ 0b0111011#7))))))
          else
            (do
              sail_assert false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .REV8 (rs1, rd) =>
    (do
      if (((←((currentlyEnabled Ext_Zbb) <||> (do
             (currentlyEnabled Ext_Zbkb)))) && (xlen == 32)) : Bool)
      then
        (pure (0b011010011000#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          if (((←((currentlyEnabled Ext_Zbb) <||> (do
                 (currentlyEnabled Ext_Zbkb)))) && (xlen == 64)) : Bool)
          then
            (pure (0b011010111000#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))
          else
            (do
              sail_assert false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .ORCB (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b001010000111#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CPOP (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CPOPW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLZ (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLZW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CTZ (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CTZW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((encdec_csrop_forwards
                    op) +++ ((encdec_reg_forwards rd) +++ 0b1110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) +++ ((imm : (BitVec 5)) +++ (1#1 +++ ((encdec_csrop_forwards op) +++ ((encdec_reg_forwards
                      rd) +++ 0b1110011#7))))))
      else
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def instruction_to_str (insn : instruction) : SailM String := do
  if ((assembly_forwards_matches insn) : Bool)
  then (assembly_forwards insn)
  else (pure (HAppend.hAppend ".insn " (BitVec.toFormatted (← (encdec_forwards insn)))))

def interruptType_to_str (i : InterruptType) : String :=
  match i with
  | .I_Reserved_0 => "reserved-interrupt-0"
  | .I_S_Software => "supervisor-software-interrupt"
  | .I_VS_Software => "virtual-supervisor-software-interrupt"
  | .I_M_Software => "machine-software-interrupt"
  | .I_Reserved_4 => "reserved-interrupt-4"
  | .I_S_Timer => "supervisor-timer-interrupt"
  | .I_VS_Timer => "virtual-supervisor-timer-interrupt"
  | .I_M_Timer => "machine-timer-interrupt"
  | .I_Reserved_8 => "reserved-interrupt-8"
  | .I_S_External => "supervisor-external-interrupt"
  | .I_VS_External => "virtual-supervisor-external-interrupt"
  | .I_M_External => "machine-external-interrupt"
  | .I_SG_External => "supervisor guest-external-interrupt"
  | .I_COF => "counter-overflow interrupt"

def misaligned_fault_str_backwards (arg_ : String) : SailM misaligned_fault := do
  match arg_ with
  | "NoFault" => (pure NoFault)
  | "AccessFault" => (pure AccessFault)
  | "AlignmentFault" => (pure AlignmentFault)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def misaligned_fault_str_forwards (arg_ : misaligned_fault) : String :=
  match arg_ with
  | .NoFault => "NoFault"
  | .AccessFault => "AccessFault"
  | .AlignmentFault => "AlignmentFault"

def reservability_str_forwards (arg_ : Reservability) : String :=
  match arg_ with
  | .RsrvNone => "RsrvNone"
  | .RsrvNonEventual => "RsrvNonEventual"
  | .RsrvEventual => "RsrvEventual"

def pma_attributes_to_str (attr : PMA) : String :=
  (HAppend.hAppend
    (if (attr.cacheable : Bool)
    then " cacheable"
    else "")
    (HAppend.hAppend
      (if (attr.coherent : Bool)
      then " coherent"
      else "")
      (HAppend.hAppend
        (if (attr.executable : Bool)
        then " executable"
        else "")
        (HAppend.hAppend
          (if (attr.readable : Bool)
          then " readable"
          else "")
          (HAppend.hAppend
            (if (attr.writable : Bool)
            then " writable"
            else "")
            (HAppend.hAppend
              (if (attr.read_idempotent : Bool)
              then " read-idempotent"
              else "")
              (HAppend.hAppend
                (if (attr.write_idempotent : Bool)
                then " write-idempotent"
                else "")
                (HAppend.hAppend " misaligned_fault:"
                  (HAppend.hAppend (misaligned_fault_str_forwards attr.misaligned_fault)
                    (HAppend.hAppend " "
                      (HAppend.hAppend (atomic_support_str_forwards attr.atomic_support)
                        (HAppend.hAppend " "
                          (HAppend.hAppend (reservability_str_forwards attr.reservability)
                            (HAppend.hAppend
                              (if (attr.supports_cbo_zero : Bool)
                              then " supports-cbo-zero"
                              else "")
                              (HAppend.hAppend
                                (if (attr.supports_pte_read : Bool)
                                then " supports-pte-read"
                                else "")
                                (if (attr.supports_pte_write : Bool)
                                then " supports-pte-write"
                                else ""))))))))))))))))

def pma_region_to_str (region : PMA_Region) : String :=
  (HAppend.hAppend "base: "
    (HAppend.hAppend (BitVec.toFormatted region.base)
      (HAppend.hAppend " size: "
        (HAppend.hAppend (BitVec.toFormatted region.size) (pma_attributes_to_str region.attributes)))))

def ptw_error_to_str (e : PTW_Error) : String :=
  match e with
  | .PTW_Invalid_Addr () => "invalid-source-addr"
  | .PTW_No_Access () => "mem-access-error"
  | .PTW_Invalid_PTE () => "invalid-pte"
  | .PTW_No_Permission () => "no-permission"
  | .PTW_Misaligned () => "misaligned-superpage"
  | .PTW_PTE_Needs_Update () => "pte-update-needed"
  | .PTW_Ext_Error _ => "extension-error"

def reservability_str_backwards (arg_ : String) : SailM Reservability := do
  match arg_ with
  | "RsrvNone" => (pure RsrvNone)
  | "RsrvNonEventual" => (pure RsrvNonEventual)
  | "RsrvEventual" => (pure RsrvEventual)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def trapCause_to_str (t : TrapCause) : String :=
  match t with
  | .Interrupt i => (HAppend.hAppend "int#" (interruptType_to_str i))
  | .Exception e => (HAppend.hAppend "exc#" (exceptionType_to_str e))

def wait_name_backwards (arg_ : String) : SailM WaitReason := do
  match arg_ with
  | "WAIT-WFI" => (pure WAIT_WFI)
  | "WAIT-WRS-STO" => (pure WAIT_WRS_STO)
  | "WAIT-WRS-NTO" => (pure WAIT_WRS_NTO)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def wait_name_forwards (arg_ : WaitReason) : String :=
  match arg_ with
  | .WAIT_WFI => "WAIT-WFI"
  | .WAIT_WRS_STO => "WAIT-WRS-STO"
  | .WAIT_WRS_NTO => "WAIT-WRS-NTO"

/-- Type quantifiers: k_a : Type -/
def is_load_store (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .Load _ => true
  | .Store _ => true
  | .LoadReserved _ => true
  | .StoreConditional _ => true
  | .Atomic _ => true
  | .InstructionFetch _ => false
  | .CacheAccess _ => true

/-- Type quantifiers: k_a : Type -/
def is_prefetch_access (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .CacheAccess (.CB_prefetch _) => true
  | _ => false

/-- Type quantifiers: k_a : Type -/
def is_store_conditional (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .StoreConditional _ => true
  | _ => false

def undefined_CSRAccessType (_ : Unit) : SailM CSRAccessType := do
  (internal_pick [CSRRead, CSRWrite, CSRReadWrite])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CSRAccessType_of_num (arg_ : Nat) : CSRAccessType :=
  match arg_ with
  | 0 => CSRRead
  | 1 => CSRWrite
  | _ => CSRReadWrite

def num_of_CSRAccessType (arg_ : CSRAccessType) : Int :=
  match arg_ with
  | .CSRRead => 0
  | .CSRWrite => 1
  | .CSRReadWrite => 2

def undefined_InterruptType (_ : Unit) : SailM InterruptType := do
  (internal_pick
    [I_Reserved_0, I_S_Software, I_VS_Software, I_M_Software, I_Reserved_4, I_S_Timer, I_VS_Timer, I_M_Timer, I_Reserved_8, I_S_External, I_VS_External, I_M_External, I_SG_External, I_COF])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def InterruptType_of_num (arg_ : Nat) : InterruptType :=
  match arg_ with
  | 0 => I_Reserved_0
  | 1 => I_S_Software
  | 2 => I_VS_Software
  | 3 => I_M_Software
  | 4 => I_Reserved_4
  | 5 => I_S_Timer
  | 6 => I_VS_Timer
  | 7 => I_M_Timer
  | 8 => I_Reserved_8
  | 9 => I_S_External
  | 10 => I_VS_External
  | 11 => I_M_External
  | 12 => I_SG_External
  | _ => I_COF

def num_of_InterruptType (arg_ : InterruptType) : Int :=
  match arg_ with
  | .I_Reserved_0 => 0
  | .I_S_Software => 1
  | .I_VS_Software => 2
  | .I_M_Software => 3
  | .I_Reserved_4 => 4
  | .I_S_Timer => 5
  | .I_VS_Timer => 6
  | .I_M_Timer => 7
  | .I_Reserved_8 => 8
  | .I_S_External => 9
  | .I_VS_External => 10
  | .I_M_External => 11
  | .I_SG_External => 12
  | .I_COF => 13

def interruptType_bits_forwards (arg_ : InterruptType) : (BitVec 6) :=
  match arg_ with
  | .I_Reserved_0 => 0b000000#6
  | .I_S_Software => 0b000001#6
  | .I_VS_Software => 0b000010#6
  | .I_M_Software => 0b000011#6
  | .I_Reserved_4 => 0b000100#6
  | .I_S_Timer => 0b000101#6
  | .I_VS_Timer => 0b000110#6
  | .I_M_Timer => 0b000111#6
  | .I_Reserved_8 => 0b001000#6
  | .I_S_External => 0b001001#6
  | .I_VS_External => 0b001010#6
  | .I_M_External => 0b001011#6
  | .I_SG_External => 0b001100#6
  | .I_COF => 0b001101#6

def interruptType_bits_backwards (arg_ : (BitVec 6)) : SailM InterruptType := do
  match arg_ with
  | 0b000000 => (pure I_Reserved_0)
  | 0b000001 => (pure I_S_Software)
  | 0b000010 => (pure I_VS_Software)
  | 0b000011 => (pure I_M_Software)
  | 0b000100 => (pure I_Reserved_4)
  | 0b000101 => (pure I_S_Timer)
  | 0b000110 => (pure I_VS_Timer)
  | 0b000111 => (pure I_M_Timer)
  | 0b001000 => (pure I_Reserved_8)
  | 0b001001 => (pure I_S_External)
  | 0b001010 => (pure I_VS_External)
  | 0b001011 => (pure I_M_External)
  | 0b001100 => (pure I_SG_External)
  | 0b001101 => (pure I_COF)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def interruptType_bits_forwards_matches (arg_ : InterruptType) : Bool :=
  match arg_ with
  | .I_Reserved_0 => true
  | .I_S_Software => true
  | .I_VS_Software => true
  | .I_M_Software => true
  | .I_Reserved_4 => true
  | .I_S_Timer => true
  | .I_VS_Timer => true
  | .I_M_Timer => true
  | .I_Reserved_8 => true
  | .I_S_External => true
  | .I_VS_External => true
  | .I_M_External => true
  | .I_SG_External => true
  | .I_COF => true

def interruptType_bits_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000001 => true
  | 0b000010 => true
  | 0b000011 => true
  | 0b000100 => true
  | 0b000101 => true
  | 0b000110 => true
  | 0b000111 => true
  | 0b001000 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b001100 => true
  | 0b001101 => true
  | _ => false

def undefined_breakpoint_cause (_ : Unit) : SailM breakpoint_cause := do
  (internal_pick [Brk_Software, Brk_Hardware])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def breakpoint_cause_of_num (arg_ : Nat) : breakpoint_cause :=
  match arg_ with
  | 0 => Brk_Software
  | _ => Brk_Hardware

def num_of_breakpoint_cause (arg_ : breakpoint_cause) : Int :=
  match arg_ with
  | .Brk_Software => 0
  | .Brk_Hardware => 1

def exceptionType_bits_forwards (arg_ : ExceptionType) : (BitVec 6) :=
  match arg_ with
  | .E_Fetch_Addr_Align () => 0b000000#6
  | .E_Fetch_Access_Fault () => 0b000001#6
  | .E_Illegal_Instr () => 0b000010#6
  | .E_Load_Addr_Align () => 0b000100#6
  | .E_Load_Access_Fault () => 0b000101#6
  | .E_SAMO_Addr_Align () => 0b000110#6
  | .E_SAMO_Access_Fault () => 0b000111#6
  | .E_U_EnvCall () => 0b001000#6
  | .E_S_EnvCall () => 0b001001#6
  | .E_VS_EnvCall () => 0b001010#6
  | .E_M_EnvCall () => 0b001011#6
  | .E_Fetch_Page_Fault () => 0b001100#6
  | .E_Load_Page_Fault () => 0b001101#6
  | .E_Reserved_14 () => 0b001110#6
  | .E_SAMO_Page_Fault () => 0b001111#6
  | .E_Reserved_16 () => 0b010000#6
  | .E_Reserved_17 () => 0b010001#6
  | .E_Software_Check () => 0b010010#6
  | .E_Reserved_19 () => 0b010011#6
  | .E_Fetch_GPage_Fault () => 0b010100#6
  | .E_Load_GPage_Fault () => 0b010101#6
  | .E_Virtual_Instr () => 0b010110#6
  | .E_SAMO_GPage_Fault () => 0b010111#6
  | .E_Breakpoint .Brk_Software => 0b000011#6
  | .E_Breakpoint .Brk_Hardware => 0b000011#6
  | .E_Extension e => (ext_exc_type_bits_forwards e)

def exceptionType_bits_backwards (arg_ : (BitVec 6)) : SailM ExceptionType := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some (E_Fetch_Addr_Align ())))
    | 0b000001 => (pure (some (E_Fetch_Access_Fault ())))
    | 0b000010 => (pure (some (E_Illegal_Instr ())))
    | 0b000100 => (pure (some (E_Load_Addr_Align ())))
    | 0b000101 => (pure (some (E_Load_Access_Fault ())))
    | 0b000110 => (pure (some (E_SAMO_Addr_Align ())))
    | 0b000111 => (pure (some (E_SAMO_Access_Fault ())))
    | 0b001000 => (pure (some (E_U_EnvCall ())))
    | 0b001001 => (pure (some (E_S_EnvCall ())))
    | 0b001010 => (pure (some (E_VS_EnvCall ())))
    | 0b001011 => (pure (some (E_M_EnvCall ())))
    | 0b001100 => (pure (some (E_Fetch_Page_Fault ())))
    | 0b001101 => (pure (some (E_Load_Page_Fault ())))
    | 0b001110 => (pure (some (E_Reserved_14 ())))
    | 0b001111 => (pure (some (E_SAMO_Page_Fault ())))
    | 0b010000 => (pure (some (E_Reserved_16 ())))
    | 0b010001 => (pure (some (E_Reserved_17 ())))
    | 0b010010 => (pure (some (E_Software_Check ())))
    | 0b010011 => (pure (some (E_Reserved_19 ())))
    | 0b010100 => (pure (some (E_Fetch_GPage_Fault ())))
    | 0b010101 => (pure (some (E_Load_GPage_Fault ())))
    | 0b010110 => (pure (some (E_Virtual_Instr ())))
    | 0b010111 => (pure (some (E_SAMO_GPage_Fault ())))
    | 0b000011 => (pure (some (E_Breakpoint Brk_Software)))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some (E_Extension e))))
        else (pure none))) with
  | .some result => (pure result)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def exceptionType_bits_forwards_matches (arg_ : ExceptionType) : Bool :=
  match arg_ with
  | .E_Fetch_Addr_Align () => true
  | .E_Fetch_Access_Fault () => true
  | .E_Illegal_Instr () => true
  | .E_Load_Addr_Align () => true
  | .E_Load_Access_Fault () => true
  | .E_SAMO_Addr_Align () => true
  | .E_SAMO_Access_Fault () => true
  | .E_U_EnvCall () => true
  | .E_S_EnvCall () => true
  | .E_VS_EnvCall () => true
  | .E_M_EnvCall () => true
  | .E_Fetch_Page_Fault () => true
  | .E_Load_Page_Fault () => true
  | .E_Reserved_14 () => true
  | .E_SAMO_Page_Fault () => true
  | .E_Reserved_16 () => true
  | .E_Reserved_17 () => true
  | .E_Software_Check () => true
  | .E_Reserved_19 () => true
  | .E_Fetch_GPage_Fault () => true
  | .E_Load_GPage_Fault () => true
  | .E_Virtual_Instr () => true
  | .E_SAMO_GPage_Fault () => true
  | .E_Breakpoint .Brk_Software => true
  | .E_Breakpoint .Brk_Hardware => true
  | .E_Extension e => true

def exceptionType_bits_backwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some true))
    | 0b000001 => (pure (some true))
    | 0b000010 => (pure (some true))
    | 0b000100 => (pure (some true))
    | 0b000101 => (pure (some true))
    | 0b000110 => (pure (some true))
    | 0b000111 => (pure (some true))
    | 0b001000 => (pure (some true))
    | 0b001001 => (pure (some true))
    | 0b001010 => (pure (some true))
    | 0b001011 => (pure (some true))
    | 0b001100 => (pure (some true))
    | 0b001101 => (pure (some true))
    | 0b001110 => (pure (some true))
    | 0b001111 => (pure (some true))
    | 0b010000 => (pure (some true))
    | 0b010001 => (pure (some true))
    | 0b010010 => (pure (some true))
    | 0b010011 => (pure (some true))
    | 0b010100 => (pure (some true))
    | 0b010101 => (pure (some true))
    | 0b010110 => (pure (some true))
    | 0b010111 => (pure (some true))
    | 0b000011 => (pure (some true))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def undefined_SWCheckCodes (_ : Unit) : SailM SWCheckCodes := do
  (internal_pick [LANDING_PAD_FAULT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def SWCheckCodes_of_num (arg_ : Nat) : SWCheckCodes :=
  match arg_ with
  | _ => LANDING_PAD_FAULT

def num_of_SWCheckCodes (arg_ : SWCheckCodes) : Int :=
  match arg_ with
  | .LANDING_PAD_FAULT => 0

def sw_check_code_to_bits (c : SWCheckCodes) : (BitVec 64) :=
  match c with
  | .LANDING_PAD_FAULT => (zero_extend (m := 64) 0b010#3)

def trapCause_bits_forwards (arg_ : TrapCause) : (BitVec 6) :=
  match arg_ with
  | .Interrupt i => (interruptType_bits_forwards i)
  | .Exception e => (exceptionType_bits_forwards e)

def trapCause_bits_backwards (arg_ : (BitVec 6)) : SailM TrapCause := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | mapping0_ =>
      (do
        if ((interruptType_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (interruptType_bits_backwards mapping0_)) with
            | i => (pure (some (Interrupt i))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        match head_exp_ with
        | mapping1_ =>
          (do
            if ((← (exceptionType_bits_backwards_matches mapping1_)) : Bool)
            then
              (do
                match (← (exceptionType_bits_backwards mapping1_)) with
                | e => (pure (some (Exception e))))
            else (pure none))) with
      | .some result => (pure result)
      | _ =>
        (do
          sail_assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def trapCause_bits_forwards_matches (arg_ : TrapCause) : Bool :=
  match arg_ with
  | .Interrupt i => true
  | .Exception e => true

def trapCause_bits_backwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | mapping0_ =>
      (do
        if ((interruptType_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (interruptType_bits_backwards mapping0_)) with
            | i => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        match head_exp_ with
        | mapping1_ =>
          (do
            if ((← (exceptionType_bits_backwards_matches mapping1_)) : Bool)
            then
              (do
                match (← (exceptionType_bits_backwards mapping1_)) with
                | e => (pure (some true)))
            else (pure none))) with
      | .some result => (pure result)
      | none =>
        (match head_exp_ with
        | _ => (pure false)))

def trapCause_is_interrupt (t : TrapCause) : Bool :=
  match t with
  | .Interrupt _ => true
  | .Exception _ => false

def undefined_TrapVectorMode (_ : Unit) : SailM TrapVectorMode := do
  (internal_pick [TV_Direct, TV_Vector, TV_Reserved])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TrapVectorMode_of_num (arg_ : Nat) : TrapVectorMode :=
  match arg_ with
  | 0 => TV_Direct
  | 1 => TV_Vector
  | _ => TV_Reserved

def num_of_TrapVectorMode (arg_ : TrapVectorMode) : Int :=
  match arg_ with
  | .TV_Direct => 0
  | .TV_Vector => 1
  | .TV_Reserved => 2

def trapVectorMode_of_bits (m : (BitVec 2)) : TrapVectorMode :=
  match m with
  | 0b00 => TV_Direct
  | 0b01 => TV_Vector
  | _ => TV_Reserved

def undefined_xRET_type (_ : Unit) : SailM xRET_type := do
  (internal_pick [mRET, sRET])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def xRET_type_of_num (arg_ : Nat) : xRET_type :=
  match arg_ with
  | 0 => mRET
  | _ => sRET

def num_of_xRET_type (arg_ : xRET_type) : Int :=
  match arg_ with
  | .mRET => 0
  | .sRET => 1

def undefined_ExtStatus (_ : Unit) : SailM ExtStatus := do
  (internal_pick [Off, Initial, Clean, Dirty])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ExtStatus_of_num (arg_ : Nat) : ExtStatus :=
  match arg_ with
  | 0 => Off
  | 1 => Initial
  | 2 => Clean
  | _ => Dirty

def num_of_ExtStatus (arg_ : ExtStatus) : Int :=
  match arg_ with
  | .Off => 0
  | .Initial => 1
  | .Clean => 2
  | .Dirty => 3

def extStatus_bits_forwards (arg_ : ExtStatus) : (BitVec 2) :=
  match arg_ with
  | .Off => 0b00#2
  | .Initial => 0b01#2
  | .Clean => 0b10#2
  | .Dirty => 0b11#2

def extStatus_bits_backwards (arg_ : (BitVec 2)) : ExtStatus :=
  match arg_ with
  | 0b00 => Off
  | 0b01 => Initial
  | 0b10 => Clean
  | _ => Dirty

def extStatus_bits_forwards_matches (arg_ : ExtStatus) : Bool :=
  match arg_ with
  | .Off => true
  | .Initial => true
  | .Clean => true
  | .Dirty => true

def extStatus_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def extStatus_to_bits (e : ExtStatus) : (BitVec 2) :=
  (extStatus_bits_forwards e)

def extStatus_of_bits (b : (BitVec 2)) : ExtStatus :=
  (extStatus_bits_backwards b)

def undefined_SATPMode (_ : Unit) : SailM SATPMode := do
  (internal_pick [Bare, Sv32, Sv39, Sv48, Sv57])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SATPMode_of_num (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 0 => Bare
  | 1 => Sv32
  | 2 => Sv39
  | 3 => Sv48
  | _ => Sv57

def num_of_SATPMode (arg_ : SATPMode) : Int :=
  match arg_ with
  | .Bare => 0
  | .Sv32 => 1
  | .Sv39 => 2
  | .Sv48 => 3
  | .Sv57 => 4

def satpMode_of_bits (a : Architecture) (m : (BitVec 4)) : (Option SATPMode) :=
  match (a, m) with
  | (_, 0x0) => (some Bare)
  | (.RV32, 0x1) => (some Sv32)
  | (.RV64, 0x8) => (some Sv39)
  | (.RV64, 0x9) => (some Sv48)
  | (.RV64, 0xA) => (some Sv57)
  | (_, _) => none

def undefined_WaitReason (_ : Unit) : SailM WaitReason := do
  (internal_pick [WAIT_WFI, WAIT_WRS_STO, WAIT_WRS_NTO])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def WaitReason_of_num (arg_ : Nat) : WaitReason :=
  match arg_ with
  | 0 => WAIT_WFI
  | 1 => WAIT_WRS_STO
  | _ => WAIT_WRS_NTO

def num_of_WaitReason (arg_ : WaitReason) : Int :=
  match arg_ with
  | .WAIT_WFI => 0
  | .WAIT_WRS_STO => 1
  | .WAIT_WRS_NTO => 2

def wait_name_forwards_matches (arg_ : WaitReason) : Bool :=
  match arg_ with
  | .WAIT_WFI => true
  | .WAIT_WRS_STO => true
  | .WAIT_WRS_NTO => true

def wait_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "WAIT-WFI" => true
  | "WAIT-WRS-STO" => true
  | "WAIT-WRS-NTO" => true
  | _ => false

def width_enc_backwards (arg_ : (BitVec 2)) : Int :=
  match arg_ with
  | 0b00 => 1
  | 0b01 => 2
  | 0b10 => 4
  | _ => 8

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_enc_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_enc_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def width_mnemonic_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_mnemonic_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | _ => false

def width_enc_wide_backwards (arg_ : (BitVec 3)) : SailM Int := do
  match arg_ with
  | 0b000 => (pure 1)
  | 0b001 => (pure 2)
  | 0b010 => (pure 4)
  | 0b011 => (pure 8)
  | 0b100 => (pure 16)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_enc_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_enc_wide_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | 0b100 => true
  | _ => false

def width_mnemonic_wide_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | "q" => (pure 16)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_mnemonic_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_mnemonic_wide_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | "q" => true
  | _ => false

