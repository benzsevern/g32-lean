import HodgeLean.Foundations.Program.SchoenCycleParameterAdicPowers
import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialGenerators
import HodgeLean.Foundations.Program.SchoenCycleElementaryIdealInclusion
import HodgeLean.Foundations.Program.SchoenCycleAdicRenameEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every positive indexed mixed elementary coefficient in the actual native curve-power parameters is a nonunit at the marked point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_mixed_elementary_parameter_nonunit
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (a : Fin b) (j : Fin (m a)) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ¬ IsUnit (aeval (s2e_curvePowerParameter Z n x)
      (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (X ⟨a, j⟩)).val)) := by
  dsimp only
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  have hp := s2e_positive_elementary_mem_origin (σ := Fin (m a)) (j.val + 1) (by omega)
  have h₁ := s2e_rename_preserves_origin_powers
    (fun i : Fin (m a) => (⟨a, i⟩ : Σ a, Fin (m a))) 1 _ (by simpa only [pow_one] using hp)
  have h₂ := s2e_rename_preserves_origin_powers ι 1 _ h₁
  rw [s2e_mixed_polynomial_invariant_X]
  have hmem := s2e_curve_power_aeval_preserves_powers Z n x 1 _ h₂
  simpa only [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem

#print axioms s2e_mixed_elementary_parameter_nonunit
end HodgeLean.Foundations.Program
