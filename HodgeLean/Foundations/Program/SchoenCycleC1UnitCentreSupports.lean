import HodgeLean.Foundations.Program.SchoenCycleC1StrictSupportTower

/-! # Exact strict supports through towers with empty centre supports -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- If every centre support is empty, the actual strict supports are exactly
the inverse images of their initial supports under the specified total map. -/
theorem s2e_c1_strict_support_tower_eq_of_empty_centres
    (r : ℕ) (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData)
    (I : ∀ i : Fin r, (X i.castSucc).IdealSheafData)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t) (I i))
    (hI : ∀ i, (I i).support = ⊥) :
    ∀ i t, ((D i t).support : Set (X i)) =
      (s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹' ((D 0 t).support : Set (X 0)) := by
  intro i
  induction i using Fin.induction with
  | zero => intro t; rfl
  | succ j ih =>
    intro t
    rw [hD j t]
    unfold s2c_strictTransform
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal, hI j,
      Closeds.coe_bot, Set.sdiff_empty]
    change closure ((b j) ⁻¹' ((D j.castSucc t).support : Set (X j.castSucc))) = _
    rw [((D j.castSucc t).support.isClosed.preimage (b j).continuous).closure_eq, ih t,
      s2e_towerTotalMap_succ]
    rfl

end HodgeLean.Foundations.Program
