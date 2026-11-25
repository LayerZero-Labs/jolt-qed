/-
Step f: the code bytes stay intact through the run.

Jolt fetches instructions from the committed bytecode, never from RAM, while Sail's model fetches
from memory. The two agree only while the bytes of the instruction rows in memory are the image's.
This file states that as a Jolt-side invariant (`JoltCodeIntact`), shows that it gives the Sail-side
`CodeIntact` that `block_simulates_decoded` needs (`CodeIntact.of_related`), that it holds at the
start of every honest trace (`JoltCodeIntact.initial`), and that every block keeps it
(`JoltCodeIntact.of_block`).
Every code byte lies in Jolt's protected code region, whose doublewords the tracer's store check
(`protected_store_ok`) keeps unchanged: a store that would change one of them fails, and a block
that runs has no failing store.
-/
import JoltConstraints.theorems.WholeRun.Elf

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false
noncomputable section

namespace WholeRun

-- Reuse the established implementation lemma without changing its module.
open private layout_memLow from JoltConstraints.theorems.WholeRun.Bundles

/-- **The code lies in Jolt's memory unchanged and protected.** Jolt's memory map `jt.sail.mem`
holds the image byte (`imageByte?`) at every byte of every instruction row, reading a missing
byte as zero, and Jolt's store check protects that byte (`protected_byte`). The image ends at or
below the heap end, so that the code is inside the range Sail's memory holds
(`Related.present`).
This is the Jolt-side version of `CodeIntact`: `CodeIntact.of_related` carries it to Sail.
For example, at the start of a run Jolt's loader has written the ELF's bytes at their addresses
and the code region covers every row (`JoltCodeIntact.initial`). -/
def JoltCodeIntact (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState) : Prop :=
  program.program_end.toNat ≤ jt.jolt_device.memory_layout.heap_end.toNat ∧
  ∀ row ∈ program.instructions, ∀ k, k < (if row.is_compressed then 2 else 4) →
    ∀ b, imageByte? program (row.address.toNat + k) = some b →
      JoltISA.Mmu.ram_byte jt.sail.mem (row.address.toNat + k) = b ∧
        JoltISA.Mmu.protected_byte jt (row.address.toNat + k) = true

/-- **Sail's memory holds the code too.** If Jolt's memory holds the image's code and Sail's state
is related to Jolt's, Sail's memory holds it: Sail has a byte at every address up to the end of the
heap, and where it does it is Jolt's. -/
theorem CodeIntact.of_related {program : Rv64ProgramImage SourceInstruction}
    {jt : SailJoltState} {s : SailState} (hrel : Related jt s) (h : JoltCodeIntact program jt) :
    CodeIntact program s := by
  intro row hrow k hk b hb
  obtain ⟨hR, hend⟩ := imageByte?_bounds program hb
  have hjt := (h.2 row hrow k hk b hb).1
  have hlow := layout_memLow jt hrel.layout
  obtain ⟨b', hb'⟩ := hrel.present (row.address.toNat + k) (by omega)
    (by
      obtain ⟨config, built⟩ := hrel.layout
      have backed := heap_end_le_ram_backing_end jt.jolt_device config built
      unfold memHigh
      have := h.1
      omega)
  have hram := hrel.ram (row.address.toNat + k)
  simp only [JoltISA.Mmu.ram_byte, hb', Option.getD_some] at hram
  simp only [JoltISA.Mmu.ram_byte] at hjt
  rw [hb', hram, hjt]

/-- **Every block keeps the code.** A block that runs keeps the layout, the code region and every
protected byte (`JoltIOSetupFrame.execProgram_memory`), and every code byte is protected. -/
theorem JoltCodeIntact.of_block {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) (h : JoltCodeIntact program b.pre) :
    JoltCodeIntact program b.post := by
  obtain ⟨instrs, -, hrun⟩ := hruns.executes
  have hkeep := JoltIOSetupFrame.execProgram_memory _ _ _ _ hrun
  refine ⟨by rw [hkeep.layout]; exact h.1, ?_⟩
  intro row hrow k hk b' hb'
  obtain ⟨hbyte, hprot⟩ := h.2 row hrow k hk b' hb'
  refine ⟨(hkeep.bytes _ hprot).trans hbyte, ?_⟩
  rw [JoltISA.Mmu.protected_byte_congr _ hkeep.layout hkeep.code]
  exact hprot

/-- A byte of a source covered by the code region, counted from the lowest address of the layout,
is protected. -/
private theorem protected_of_covers (jt : SailJoltState) {x : BitVec 64 × Bool}
    (hlow : jt.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0)
    (hcov : RegionCovers jt.jolt_device.memory_layout.get_lowest_address.toNat jt.codeRegion x)
    {k : Nat} (hk : k < (if x.2 then 2 else 4)) :
    JoltISA.Mmu.protected_byte jt (x.1.toNat + k) = true := by
  obtain ⟨hge, -, hfirst, hlast⟩ := hcov
  have hw : (if x.2 then 2 else 4) ≤ 4 := by split <;> omega
  simp only [JoltISA.Mmu.protected_byte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨by omega, by omega⟩)))

/-- **The code starts intact.** In the initial state of every honest trace, Jolt's memory map
holds the image's bytes, the image ends below the heap end, and the code region, which the
loader computes from the program's rows, covers every row that has an image byte. -/
theorem JoltCodeIntact.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    JoltCodeIntact joltInstance.program trace.initialState := by
  have built := trace.initialized
  refine ⟨JoltConstraints.initial_state_program_end_le_heap_end joltInstance privateInputs _ built,
    ?_⟩
  intro row hrow k hk b hb
  refine ⟨?_, ?_⟩
  · have hget : trace.initialState.sail.mem.get? (row.address.toNat + k) = some b :=
      sailInit_get?_image joltInstance privateInputs _ built _ b hb
    simp only [JoltISA.Mmu.ram_byte, hget, Option.getD_some]
  · obtain ⟨layout, _, _, _, _, hinit⟩ :=
      initial_state_build joltInstance privateInputs _ built
    obtain ⟨region, mem, hregion, -, hshape⟩ :=
      JoltConstraints.initialState_shape _ _ _ _ _ _ hinit
    have hx : (row.address, row.is_compressed) ∈
        joltInstance.program.instructions.toList.map fun row => (row.address, row.is_compressed) :=
      List.mem_map.mpr ⟨row, Array.mem_toList_iff.mpr hrow, rfl⟩
    have hne : row.address ≠ 0 := by
      intro h0
      have := (imageByte?_bounds _ hb).1
      rw [h0] at this
      unfold JoltISA.RAM_START_ADDRESS at this
      simp at this
      split at hk <;> omega
    rw [codeRegionOf_eq] at hregion
    obtain ⟨hlow, hcov⟩ := codeRegionAt_covers hregion hx hne
    refine protected_of_covers trace.initialState (x := (row.address, row.is_compressed)) ?_ ?_ hk
    · rw [hshape]; exact hlow
    · rw [hshape]; exact hcov

end WholeRun
