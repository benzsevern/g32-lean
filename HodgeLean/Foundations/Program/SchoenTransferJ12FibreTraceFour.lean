import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTrace
import Mathlib.Tactic.FinCases

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program

/-- In total degree four the fibre trace discards every external component outside fibre degree two. -/
theorem s4_selected_fibre_trace_four_off_degree
    (T Y : TopCat.{0})
    (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p))
    (I : Cohomology ℚ Y 2 ≃ₗ[ℚ] ℚ)
    (q : Fin 5) (hq : q.val ≠ 2)
    (b : Cohomology ℚ Y q.val) (a : Cohomology ℚ T (4 - q.val)) :
    s4_selected_fibre_trace T Y hY 2 2 I
      (cup (TopCat.of (T × Y)) (by have := q.isLt; omega)
        (cohomologyMap ℚ q.val (productSecond T Y) b)
        (cohomologyMap ℚ (4 - q.val) (productFirst T Y) a)) = 0 := by
  fin_cases q
  all_goals try (norm_num at hq)
  all_goals
    let swap : TopCat.of (Y × T) ⟶ TopCat.of (T × Y) :=
      TopCat.ofHom ⟨Prod.swap, continuous_swap⟩
    have h1 : cohomologyMap ℚ _ swap
        (cohomologyMap ℚ _ (productSecond T Y) b) =
        cohomologyMap ℚ _ (productFirst Y T) b := by
      rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
      rfl
    have h2 : cohomologyMap ℚ _ swap
        (cohomologyMap ℚ _ (productFirst T Y) a) =
        cohomologyMap ℚ _ (productSecond Y T) a := by
      rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
      rfl
    have hs := rationalProductCohomologyEquiv_tmul Y T hY _ _ b a
    unfold s4_selected_fibre_trace
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [cohomologyMap_cup, h1, h2, ← hs]
    simp only [Fin.val_mk, Nat.reduceSub, Nat.reduceAdd, LinearEquiv.symm_apply_apply]
    simp [DirectSum.component.of]

#print axioms s4_selected_fibre_trace_four_off_degree
end HodgeLean.Foundations.Program
