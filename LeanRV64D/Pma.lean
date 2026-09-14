import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.MemAddrtype
import LeanRV64D.RangeUtil

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace LeanRV64D.Functions

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

def undefined_AtomicSupport (_ : Unit) : SailM AtomicSupport := do
  (internal_pick [AMONone, AMOSwap, AMOLogical, AMOArithmetic, AMOCASW, AMOCASD, AMOCASQ])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def AtomicSupport_of_num (arg_ : Nat) : AtomicSupport :=
  match arg_ with
  | 0 => AMONone
  | 1 => AMOSwap
  | 2 => AMOLogical
  | 3 => AMOArithmetic
  | 4 => AMOCASW
  | 5 => AMOCASD
  | _ => AMOCASQ

def atomic_support_str_forwards_matches (arg_ : AtomicSupport) : Bool :=
  match arg_ with
  | AMONone => true
  | AMOSwap => true
  | AMOLogical => true
  | AMOArithmetic => true
  | AMOCASW => true
  | AMOCASD => true
  | AMOCASQ => true

def atomic_support_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "AMONone" => true
  | "AMOSwap" => true
  | "AMOLogical" => true
  | "AMOArithmetic" => true
  | "AMOCASW" => true
  | "AMOCASD" => true
  | "AMOCASQ" => true
  | _ => false

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pma_allows_atomic_op (pma : AtomicSupport) (op : amoop) (width : Nat) : Bool :=
  match pma with
  | AMONone => false
  | AMOSwap => (op == AMOSWAP)
  | AMOLogical => ((op == AMOSWAP) || ((op == AMOAND) || ((op == AMOOR) || (op == AMOXOR))))
  | AMOArithmetic => (bne op AMOCAS)
  | AMOCASW => ((bne op AMOCAS) || (width == 4))
  | AMOCASD => ((bne op AMOCAS) || ((width == 4) || (width == 8)))
  | AMOCASQ => ((bne op AMOCAS) || ((width == 4) || ((width == 8) || (width == 16))))

def undefined_Reservability (_ : Unit) : SailM Reservability := do
  (internal_pick [RsrvNone, RsrvNonEventual, RsrvEventual])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Reservability_of_num (arg_ : Nat) : Reservability :=
  match arg_ with
  | 0 => RsrvNone
  | 1 => RsrvNonEventual
  | _ => RsrvEventual

def num_of_Reservability (arg_ : Reservability) : Int :=
  match arg_ with
  | RsrvNone => 0
  | RsrvNonEventual => 1
  | RsrvEventual => 2

def reservability_str_forwards_matches (arg_ : Reservability) : Bool :=
  match arg_ with
  | RsrvNone => true
  | RsrvNonEventual => true
  | RsrvEventual => true

def reservability_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "RsrvNone" => true
  | "RsrvNonEventual" => true
  | "RsrvEventual" => true
  | _ => false

def undefined_misaligned_fault (_ : Unit) : SailM misaligned_fault := do
  (internal_pick [NoFault, AccessFault, AlignmentFault])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def misaligned_fault_of_num (arg_ : Nat) : misaligned_fault :=
  match arg_ with
  | 0 => NoFault
  | 1 => AccessFault
  | _ => AlignmentFault

def num_of_misaligned_fault (arg_ : misaligned_fault) : Int :=
  match arg_ with
  | NoFault => 0
  | AccessFault => 1
  | AlignmentFault => 2

def misaligned_fault_str_forwards_matches (arg_ : misaligned_fault) : Bool :=
  match arg_ with
  | NoFault => true
  | AccessFault => true
  | AlignmentFault => true

def misaligned_fault_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "NoFault" => true
  | "AccessFault" => true
  | "AlignmentFault" => true
  | _ => false

def undefined_PMA (_ : Unit) : SailM PMA := do
  (pure { cacheable := ← (undefined_bool ())
          coherent := ← (undefined_bool ())
          executable := ← (undefined_bool ())
          readable := ← (undefined_bool ())
          writable := ← (undefined_bool ())
          read_idempotent := ← (undefined_bool ())
          write_idempotent := ← (undefined_bool ())
          misaligned_fault := ← (undefined_misaligned_fault ())
          atomic_support := ← (undefined_AtomicSupport ())
          reservability := ← (undefined_Reservability ())
          supports_cbo_zero := ← (undefined_bool ())
          supports_pte_read := ← (undefined_bool ())
          supports_pte_write := ← (undefined_bool ()) })

def undefined_PMA_Region (_ : Unit) : SailM PMA_Region := do
  (pure { base := ← (undefined_bitvector 64)
          size := ← (undefined_bitvector 64)
          attributes := ← (undefined_PMA ())
          include_in_device_tree := ← (undefined_bool ()) })

def matching_pma_bits_range (pmas : (List PMA_Region)) (base : (BitVec 64)) (size : (BitVec 64)) : (Option PMA_Region) :=
  match pmas with
  | [] => none
  | (pma :: rest) =>
    (if ((range_subset base size pma.base pma.size) : Bool)
    then (some pma)
    else (matching_pma_bits_range rest base size))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def matching_pma (pmas : (List PMA_Region)) (addr : physaddr) (width : Nat) : (Option PMA_Region) :=
  (matching_pma_bits_range pmas (zero_extend (m := 64) (bits_of_physaddr addr))
    (to_bits (l := 64) width))

