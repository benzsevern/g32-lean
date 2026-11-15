import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineProjectiveImage
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveBooleanValues

/-! # Literal Boolean images under original projective affine chart morphisms -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.ComplexTopology HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual affine finite type scheme mapped through an original projective affine chart has its literal image in the specified Boolean projective model.
Source: Marked.evaluate_appLE; properCycle_affine_projective_matrix_image; properCycle_projective_boolean_affine_chart.
HC no distance; AV milestone no distance. -/
theorem properCycle_affine_chart_projective_image (n : ℕ) (i : Fin (n+1))
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (ψ : X ⟶ Over.mk (complexAffineSpace (Fin (n+1)) ↘ Spec ↧ℂ)) :
    ∃ B : s2v_t11b_Formula (Fintype.card
      ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))),
      B.realize = Set.range (fun x : ComplexPoint X =>
        (properCycle_projective_boolean_homeomorph n
          (chartAffineComplexPointMap i (Point.map ψ x))).val) := by
  classical
  let t (j : Fin (n+1)) : Γ(X.left, ⊤) :=
    ψ.left.appLE ⊤ ⊤ (by simp) (AffineSpace.coord (Spec ↧ℂ) j)
  let s := Function.update t i 1
  have ht (x : ComplexPoint X) (j : Fin (n+1)) :
      Point.evaluate ⊤ (t j) x = affineSpaceEquiv (Fin (n+1)) (Point.map ψ x) j := by
    rw [← Marked.evaluate_appLE ψ ⊤ ⊤ (by simp) _ x (by trivial), evaluate_top_eq_appTop]
    rfl
  have he (x : ComplexPoint X) : (fun j => Point.evaluate ⊤ (s j) x) =
      Function.update (affineSpaceEquiv (Fin (n+1)) (Point.map ψ x)) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [s, evaluate_top_eq_appTop]
    · simpa only [s, Function.update_of_ne hji] using ht x j
  have hs (x : ComplexPoint X) : (fun j => Point.evaluate ⊤ (s j) x) ≠ 0 := by
    rw [he]
    exact vector_ne_zero_of_coordinate _ i (by simp)
  obtain ⟨B, hB⟩ := properCycle_affine_projective_matrix_image X s hs
  refine ⟨B, hB.trans ?_⟩
  congr 1
  funext x
  rw [properCycle_projective_boolean_affine_chart, ← he x]

end HodgeLean.Foundations.QuotientDuality
