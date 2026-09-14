import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.Xlen
import LeanRV64D.PlatformConfig
import LeanRV64D.Extensions
import LeanRV64D.Types
import LeanRV64D.Callbacks
import LeanRV64D.Regs
import LeanRV64D.PcAccess
import LeanRV64D.SysRegs
import LeanRV64D.InterruptRegs
import LeanRV64D.SysExceptions
import LeanRV64D.PmpRegs
import LeanRV64D.PmpControl
import LeanRV64D.StateenRegs
import LeanRV64D.VextRegs
import LeanRV64D.ZicfilpRegs
import LeanRV64D.StateenAccessChecks

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
  | User => (pure 0b00#2)
  | VirtualUser => (pure 0b00#2)
  | Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure 0b10#2)
      else (pure 0b01#2))
  | VirtualSupervisor => (pure 0b01#2)
  | Machine => (pure 0b11#2)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (zopz0zKzJ_u (← (privLevel_to_CSR_privbits p)) (csrPriv csr)))

def check_CSR_access (csr : (BitVec 12)) (access_type : CSRAccessType) : Bool :=
  (not (((access_type == CSRWrite) || (access_type == CSRReadWrite)) && ((csrAccess csr) == 0b11#2)))

def is_ssp_accessible (priv : Privilege) : SailM Bool := do
  match priv with
  | Machine => (pure true)
  | Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg))))
  | VirtualSupervisor =>
    (internal_error "extensions/cfi/zicfiss_regs.sail" 40 "Hypervisor extension not supported")
  | VirtualUser =>
    (internal_error "extensions/cfi/zicfiss_regs.sail" 43 "Hypervisor extension not supported")
  | User =>
    (pure (((← (currentlyEnabled Ext_S)) && (bool_bit_backwards
            (_get_SEnvcfg_SSE (← (read_senvcfg ()))))) || (bool_bit_backwards
          (_get_MEnvcfg_SSE (← readReg menvcfg)))))

def sstc_CSRs_accessible (priv : Privilege) : SailM Bool := do
  (pure ((priv == Machine) || ((priv == Supervisor) && (((_get_Counteren_TM (← readReg mcounteren)) == 1#1) && ((_get_MEnvcfg_STCE
              (← readReg menvcfg)) == 1#1)))))

def is_CSR_accessible (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : CSRAccessType) : SailM Bool := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (0x301, g__2, g__3) => (pure true)
  | (0x300, g__4, g__5) => (pure true)
  | (0x310, g__6, g__7) => (pure (xlen == 32))
  | (0x747, g__8, g__9) => (pure ((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)))
  | (0x757, g__10, g__11) =>
    (pure (((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)) && (xlen == 32)))
  | (0x30A, g__12, g__13) => (currentlyEnabled Ext_U)
  | (0x31A, g__14, g__15) => (pure ((← (currentlyEnabled Ext_U)) && (xlen == 32)))
  | (0x10A, g__16, g__17) => (currentlyEnabled Ext_S)
  | (0x342, g__18, g__19) => (pure true)
  | (0x343, g__20, g__21) => (pure true)
  | (0x340, g__22, g__23) => (pure true)
  | (0x106, g__24, g__25) => (currentlyEnabled Ext_S)
  | (0x306, g__26, g__27) => (currentlyEnabled Ext_U)
  | (0x320, g__28, g__29) => (pure true)
  | (0xF11, g__30, g__31) => (pure true)
  | (0xF12, g__32, g__33) => (pure true)
  | (0xF13, g__34, g__35) => (pure true)
  | (0xF14, g__36, g__37) => (pure true)
  | (0xF15, g__38, g__39) => (pure true)
  | (0x100, g__40, g__41) => (currentlyEnabled Ext_S)
  | (0x140, g__42, g__43) => (currentlyEnabled Ext_S)
  | (0x142, g__44, g__45) => (currentlyEnabled Ext_S)
  | (0x143, g__46, g__47) => (currentlyEnabled Ext_S)
  | (0x7A0, g__48, g__49) => (pure true)
  | (0x304, g__50, g__51) => (pure true)
  | (0x344, g__52, g__53) => (pure true)
  | (0x302, g__54, g__55) => (currentlyEnabled Ext_S)
  | (0x312, g__56, g__57) => (pure ((← (currentlyEnabled Ext_S)) && (xlen == 32)))
  | (0x303, g__58, g__59) => (currentlyEnabled Ext_S)
  | (0x144, g__60, g__61) => (currentlyEnabled Ext_S)
  | (0x104, g__62, g__63) => (currentlyEnabled Ext_S)
  | (0x105, g__64, g__65) => (currentlyEnabled Ext_S)
  | (0x141, g__66, g__67) => (currentlyEnabled Ext_S)
  | (0x305, g__68, g__69) => (pure true)
  | (0x341, g__70, g__71) => (pure true)
  | (v__3840, g__72, g__73) =>
    (do
      if (((Sail.BitVec.extractLsb v__3840 11 4) == (0x3A#8 : (BitVec 8))) : Bool)
      then
        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__3840 3 0)
        (pure ((sys_pmp_count >b (4 *i (BitVec.toNatInt idx))) && (((BitVec.access idx 0) == 0#1) || (xlen == 32)))))
      else
        (do
          if (((Sail.BitVec.extractLsb v__3840 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__3840 3 0)
            (pure (sys_pmp_count >b (BitVec.toNatInt (0b00#2 +++ idx)))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__3840 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__3840 3 0)
                (pure (sys_pmp_count >b (BitVec.toNatInt (0b01#2 +++ idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__3840 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__3840 3 0)
                    (pure (sys_pmp_count >b (BitVec.toNatInt (0b10#2 +++ idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__3840 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__3840 3 0)
                        (pure (sys_pmp_count >b (BitVec.toNatInt (0b11#2 +++ idx)))))
                      else
                        (do
                          match (v__3840, g__72, g__73) with
                          | (0x001, g__74, g__75) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x002, g__76, g__77) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x003, g__78, g__79) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x008, g__80, g__81) => (currentlyEnabled Ext_Zve32x)
                          | (0x009, g__82, g__83) => (currentlyEnabled Ext_Zve32x)
                          | (0x00A, g__84, g__85) => (currentlyEnabled Ext_Zve32x)
                          | (0x00F, g__86, g__87) => (currentlyEnabled Ext_Zve32x)
                          | (0xC20, g__88, g__89) => (currentlyEnabled Ext_Zve32x)
                          | (0xC21, g__90, g__91) => (currentlyEnabled Ext_Zve32x)
                          | (0xC22, g__92, g__93) => (currentlyEnabled Ext_Zve32x)
                          | (0x321, g__94, g__95) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x721, g__96, g__97) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x322, g__98, g__99) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x722, g__100, g__101) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x30C, g__102, g__103) => (pure (is_mstateen_accessible ()))
                          | (0x30D, g__104, g__105) => (pure (is_mstateen_accessible ()))
                          | (0x30E, g__106, g__107) => (pure (is_mstateen_accessible ()))
                          | (0x30F, g__108, g__109) => (pure (is_mstateen_accessible ()))
                          | (0x31C, g__110, g__111) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31D, g__112, g__113) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31E, g__114, g__115) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x31F, g__116, g__117) =>
                            (pure ((is_mstateen_accessible ()) && (xlen == 32)))
                          | (0x60C, g__118, g__119) => (is_hstateen_accessible ())
                          | (0x60D, g__120, g__121) => (is_hstateen_accessible ())
                          | (0x60E, g__122, g__123) => (is_hstateen_accessible ())
                          | (0x60F, g__124, g__125) => (is_hstateen_accessible ())
                          | (0x61C, g__126, g__127) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61D, g__128, g__129) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61E, g__130, g__131) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x61F, g__132, g__133) =>
                            (pure ((xlen == 32) && (← (is_hstateen_accessible ()))))
                          | (0x10C, g__134, g__135) => (is_sstateen_accessible ())
                          | (0x10D, g__136, g__137) => (is_sstateen_accessible ())
                          | (0x10E, g__138, g__139) => (is_sstateen_accessible ())
                          | (0x10F, g__140, g__141) => (is_sstateen_accessible ())
                          | (0x180, g__72, g__142) =>
                            (pure ((← (currentlyEnabled Ext_S)) && (not
                                  ((g__72 == Supervisor) && ((_get_Mstatus_TVM (← readReg mstatus)) == 1#1)))))
                          | (0x015, g__72, g__73) =>
                            (pure ((← (currentlyEnabled Ext_Zkr)) && ((bne g__73 CSRRead) && (← do
                                    match g__72 with
                                    | Machine => (pure true)
                                    | Supervisor =>
                                      (pure ((_get_Seccfg_SSEED (← readReg mseccfg)) == 1#1))
                                    | User =>
                                      (pure ((_get_Seccfg_USEED (← readReg mseccfg)) == 1#1))
                                    | VirtualSupervisor =>
                                      (internal_error "extensions/K/zkr_control.sail" 52
                                        "Hypervisor extension not supported")
                                    | VirtualUser =>
                                      (internal_error "extensions/K/zkr_control.sail" 53
                                        "Hypervisor extension not supported")))))
                          | (v__3840, g__143, g__144) =>
                            (do
                              if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b0011001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__3840 4 0)
                                   ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                              then (currentlyEnabled Ext_Zihpm)
                              else
                                (do
                                  if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b1011000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__3840 4 0)
                                       ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                                  then (currentlyEnabled Ext_Zihpm)
                                  else
                                    (do
                                      if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b1011100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__3840 4 0)
                                           ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                                      then
                                        (pure ((← (currentlyEnabled Ext_Zihpm)) && (xlen == 32)))
                                      else
                                        (do
                                          if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b1100000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__3840 4 0)
                                               ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                                          then
                                            (do
                                              let index : (BitVec 5) :=
                                                (Sail.BitVec.extractLsb v__3840 4 0)
                                              (pure ((← (currentlyEnabled Ext_Zihpm)) && ((← (currentlyEnabled
                                                        Ext_U)) && (← (counter_enabled
                                                        (BitVec.toNatInt index) g__143))))))
                                          else
                                            (do
                                              if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b1100100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__3840 4 0)
                                                   ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                                              then
                                                (do
                                                  let index : (BitVec 5) :=
                                                    (Sail.BitVec.extractLsb v__3840 4 0)
                                                  (pure ((← (currentlyEnabled Ext_Zihpm)) && ((← (currentlyEnabled
                                                            Ext_U)) && ((xlen == 32) && (← (counter_enabled
                                                              (BitVec.toNatInt index) g__143)))))))
                                              else
                                                (do
                                                  if ((((Sail.BitVec.extractLsb v__3840 11 5) == (0b0111001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__3840 4 0)
                                                       ((BitVec.toNatInt index) ≥b 3) : Bool)) : Bool)
                                                  then
                                                    (pure ((← (currentlyEnabled Ext_Sscofpmf)) && (xlen == 32)))
                                                  else
                                                    (do
                                                      match (v__3840, g__143, g__144) with
                                                      | (0xDA0, g__145, g__146) =>
                                                        (pure ((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled
                                                                Ext_S))))
                                                      | (0x14D, g__143, g__147) =>
                                                        (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled
                                                                  Ext_Sstc)) && (← (sstc_CSRs_accessible
                                                                  g__143)))))
                                                      | (0x15D, g__143, g__148) =>
                                                        (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled
                                                                  Ext_Sstc)) && ((xlen == 32) && (← (sstc_CSRs_accessible
                                                                    g__143))))))
                                                      | (0x011, g__149, g__150) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicfiss)) && (← (is_ssp_accessible
                                                                (← readReg cur_privilege)))))
                                                      | (0xC00, g__143, g__151) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled
                                                                0 g__143))))
                                                      | (0xC01, g__143, g__152) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled
                                                                1 g__143))))
                                                      | (0xC02, g__143, g__153) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled
                                                                2 g__143))))
                                                      | (0xC80, g__143, g__154) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                  0 g__143)))))
                                                      | (0xC81, g__143, g__155) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                  1 g__143)))))
                                                      | (0xC82, g__143, g__156) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                  2 g__143)))))
                                                      | (0xB00, g__157, g__158) =>
                                                        (currentlyEnabled Ext_Zicntr)
                                                      | (0xB02, g__159, g__160) =>
                                                        (currentlyEnabled Ext_Zicntr)
                                                      | (0xB80, g__161, g__162) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
                                                      | (0xB82, g__163, g__164) =>
                                                        (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
                                                      | (0x181, g__165, g__166) =>
                                                        (currentlyEnabled Ext_Ssqosid)
                                                      | _ => (pure false))))))))))))))

def check_CSR (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM Bool := do
  (pure ((← (check_CSR_priv csr p)) && ((check_CSR_access csr access_type) && ((← (is_CSR_accessible
              csr p access_type)) && (← (stateen_allows_CSR_access csr p access_type))))))

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
  assert ((← (currentlyEnabled Ext_S)) || ((← readReg mideleg) == (zeros (n := 64)))) "sys/sys_control.sail:91.58-91.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == 1#1)) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == 1#1)) || (priv == User)))
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
  | Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | User => (internal_error "sys/sys_control.sail" 169 "Invalid privilege level")
  | VirtualUser => (internal_error "sys/sys_control.sail" 170 "Hypervisor extension not supported")
  | VirtualSupervisor =>
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
  | Machine =>
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
  | Supervisor =>
    (do
      assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
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
          | User => (pure 0#1)
          | Supervisor => (pure 1#1)
          | Machine =>
            (internal_error "sys/sys_control.sail" 220 "invalid privilege for s-mode trap")
          | VirtualUser =>
            (internal_error "sys/sys_control.sail" 221 "Hypervisor extension not supported")
          | VirtualSupervisor =>
            (internal_error "sys/sys_control.sail" 222 "Hypervisor extension not supported")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg scause)))
  | User => (internal_error "sys/sys_control.sail" 235 "Invalid privilege level")
  | VirtualUser => (internal_error "sys/sys_control.sail" 236 "Hypervisor extension not supported")
  | VirtualSupervisor =>
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
     | .E_Breakpoint Brk_Software => software_breakpoint_writes_xtval
     | .E_Breakpoint Brk_Hardware => hardware_breakpoint_writes_xtval
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
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bit (hartSupports Ext_D)))
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

