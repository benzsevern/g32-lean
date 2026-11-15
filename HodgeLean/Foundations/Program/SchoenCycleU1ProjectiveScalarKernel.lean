import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveChartAlgebra

/-! # Scalar normalized projective variations give constant chart points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A scalar variation of the actual normalized projective chart vector
vanishes and makes the whole dual-number chart point constant.
Source: Hartshorne, Algebraic Geometry, II.7 and II.8, projective tangent vectors;
Mathlib, the normalized projective chart generators. -/
theorem s2e_u1_projective_chart_constant_of_scalar_variation
    {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* DualNumber ℂ)
    (hscalar : ∃ a : ℂ, (fun j => (φ (chartCoordinate i j)).snd) =
      a • (fun j => (φ (chartCoordinate i j)).fst)) :
    φ = (TrivSqZeroExt.inlHom ℂ ℂ).comp
      ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp φ) := by
  obtain ⟨a, ha⟩ := hscalar
  have hi := congrFun ha i
  simp only [Pi.smul_apply, smul_eq_mul, chartCoordinate_self, map_one,
    TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one, mul_one] at hi
  have ha0 : a = 0 := hi.symm
  subst a
  have hs (j : Fin (n + 1)) : (φ (chartCoordinate i j)).snd = 0 := by
    have hj := congrFun ha j
    simpa only [zero_smul, Pi.zero_apply] using hj
  apply s2e_u1_projective_chart_ringHom_ext i
  intro j
  apply TrivSqZeroExt.ext
  · rfl
  · exact hs j

end HodgeLean.Foundations.Program
