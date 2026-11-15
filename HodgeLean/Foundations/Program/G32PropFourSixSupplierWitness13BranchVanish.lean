import HodgeLean.Foundations.Program.G32PropFourSixPacked0494
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row13_branchTraces : Fin 24 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨2, 0⟩, ⟨1, 3⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-2, -3⟩, ⟨-1, -3⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩]

theorem g32p_row13_branchTraceCheck (i : Fin 24) :
    (⟨∑ j : Fin 4, (g32p_row13_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row13_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row13_branchTraces i := by
  revert i
  decide +kernel

theorem g32p_row13_branchCharacter (i : Fin 24) :
    g32p_rho.character (g32p_row13_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row13_branchTraces i) := by
  rw [g32p_rho_character, g32p_row13_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row13_branchTraceCheck]

theorem g32p_row13_branchTraceAvoid : ∀ i : Fin 24, ∀ j : Fin 12,
    g32p_row13_branchTraces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row13_reflectionExponents (j : Fin 12) :
    papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
      (g32p_classDatum ⟨j.val, by omega⟩) = 0 := by
  apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
    (by simpa only [if_pos j.isLt] using
      g32p_branch_power ⟨j.val, by omega⟩) g32p_rho
  intro h he
  let i := g32p_row13_groupEquiv.symm h
  have hi : g32p_row13_groupEquiv i = h := g32p_row13_groupEquiv.apply_symm_apply h
  rw [← hi, g32p_row13_branchCharacter, g32p_branch_character] at he
  exact g32p_row13_branchTraceAvoid i j
    (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)

end HodgeLean.Foundations.Program
