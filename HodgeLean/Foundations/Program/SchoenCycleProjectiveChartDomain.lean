import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartPoints

/-! # Actual standard projective chart domains -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The projection of the actual complex standard chart to integral projective space is the integral chart inclusion after tensor base change.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveChart_toProj {n : ℕ} (i : Fin (n + 1)) :
    s2e_standardProjectiveChart i ≫
      pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading n))) =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight :
          HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →ₐ[ℤ]
            ℂ ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)))) ≫
      Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one := by
  unfold s2e_standardProjectiveChart
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
    s2e_specTensorProductTerminalIso_hom_snd]

end HodgeLean.Foundations.Program
