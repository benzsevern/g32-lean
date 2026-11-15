import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalProjectiveChartKernel
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveDualChartCurve
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveConstantCurve
import HodgeLean.Foundations.Program.SchoenCycleU1DualResiduePoint

/-! # Stationary kernel for actual canonical projective dual-number maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An actual projective dual-number map whose canonical quotient is constant
at its residue point is itself constant at its residue point.
Source: ACGH, Geometry of Algebraic Curves I, Chapters I and IV; Hartshorne, II.8. -/
theorem s2e_u1_canonical_projective_dual_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k : ℕ) (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (hg : ((2 * k : ℕ) : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
        Module.finite_of_finrank_pos (by rw [hd]; omega)
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) k hd
      Point.map ℓ = fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg (ep.symm R))
    (f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (hstationary : f ≫ ℓ = s2e_u1_constantDualPoint B
      (Point.map ℓ (Point.map f s2e_u1_dualResiduePoint))) :
    f = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by
  obtain ⟨i, φ, hrep⟩ := s2e_u1_projective_dual_point_chartCurve k f
  have hb : Point.map f s2e_u1_dualResiduePoint =
      Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0) := by
    rw [← hrep]
    change Point.map (s2e_u1_projectiveChartCurve i φ)
      (Point.map s2e_u1_polynomialDualParameter s2e_u1_dualResiduePoint) = _
    rw [s2e_u1_dualResiduePoint_polynomialParameter]
  have hs : s2e_u1_polynomialDualParameter ≫ (s2e_u1_projectiveChartCurve i φ ≫ ℓ) =
      s2e_u1_constantDualPoint B
        (Point.map (s2e_u1_projectiveChartCurve i φ ≫ ℓ) (s2e_u1_polynomialParameterPoint 0)) := by
    rw [← Category.assoc, hrep, hstationary, hb]
    rfl
  have hφ := s2e_u1_canonical_projectiveChart_kernel Z B k γ hsurj hγ hquot hg hd ℓ hℓ i φ hs
  calc
    f = s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ := hrep.symm
    _ = s2e_u1_constantDualPoint _
        (Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0)) :=
      s2e_u1_projectiveChartCurve_dual_constant i φ hφ
    _ = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by rw [hb]

end HodgeLean.Foundations.Program
