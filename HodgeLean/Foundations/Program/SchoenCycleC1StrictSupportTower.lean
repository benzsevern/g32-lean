import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Actual strict branch supports under the total tower projection -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every retained strict branch support maps into its specified initial
support under the actual total tower map. -/
theorem s2e_c1_strict_support_tower_subset
    (r : ℕ) (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData)
    (I : ∀ i : Fin r, (X i.castSucc).IdealSheafData)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t) (I i)) :
    ∀ i t, ((D i t).support : Set (X i)) ⊆
      (s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹' ((D 0 t).support : Set (X 0)) := by
  intro i
  induction i using Fin.induction with
  | zero => intro t; exact Set.Subset.rfl
  | succ j ih =>
    intro t x hx
    rw [hD j t] at hx
    have hprev := s2e_strictTransform_support_subset (b j) (D j.castSucc t) (I j) hx
    have hinit := ih t hprev
    simpa only [s2e_towerTotalMap_succ, Scheme.Hom.comp_apply, Set.mem_preimage] using hinit

end HodgeLean.Foundations.Program
