import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalLineKernel
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectivePolynomialCurve
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveLineCoordinates
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveScalarKernel
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialCurveStationary

/-! # Actual canonical quotient kernels on normalized projective chart curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace Filter Topology
open HodgeLean.Adapters
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A normalized projective chart line with stationary actual canonical quotient
has a constant dual-number chart evaluation.
Source: ACGH, Geometry of Algebraic Curves I, Chapters I and IV; Hartshorne, II.8. -/
theorem s2e_u1_canonical_projectiveChart_kernel
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
    (i : Fin (k + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading.{0} k)
      (MvPolynomial.X i : UniversalRing.{0} k) →+* DualNumber ℂ)
    (hstationary : s2e_u1_polynomialDualParameter ≫
        (s2e_u1_projectiveChartCurve i φ ≫ ℓ) =
      s2e_u1_constantDualPoint B
        (Point.map (s2e_u1_projectiveChartCurve i φ ≫ ℓ)
          (s2e_u1_polynomialParameterPoint 0))) :
    φ = (TrivSqZeroExt.inlHom ℂ ℂ).comp
      ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp φ) := by
  classical
  let H := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)
  letI : FiniteDimensional ℂ H := Module.finite_of_finrank_pos (by rw [hd]; omega)
  let e := (Module.finBasisOfFinrankEq ℂ H hd).equivFun
  let v : CoordinateSpace k := fun j => (φ (chartCoordinate i j)).fst
  let w : CoordinateSpace k := fun j => (φ (chartCoordinate i j)).snd
  let θ : H := e.symm v
  let δ : H := e.symm w
  have hv (t : ℂ) : v + t • w ≠ 0 := by
    rw [← s2e_u1_projectiveChartLine_coordinates.{0, 0} i φ t]
    exact vectorOfAwayRingHom_ne_zero i _
  have hθ : θ ≠ 0 := e.symm.map_ne_zero_iff.mpr (by simpa using hv 0)
  let f := s2e_u1_projectiveChartCurve i φ ≫ ℓ
  let b : ℂ → ComplexPoint B := fun t => Point.map f (s2e_u1_polynomialParameterPoint t)
  have hline : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : θ + t • δ ≠ 0,
      b t = s2e_canonicalQuotientPoint Z B (2 * k) γ hg
        (Projectivization.mk ℂ (θ + t • δ) h) := by
    apply Filter.Eventually.of_forall
    intro t
    have htv : e.symm (v + t • w) = θ + t • δ := by simp [θ, δ]
    have ht : θ + t • δ ≠ 0 := htv ▸ e.symm.map_ne_zero_iff.mpr (hv t)
    refine ⟨ht, ?_⟩
    change Point.map ℓ (Point.map (s2e_u1_projectiveChartCurve i φ)
      (s2e_u1_polynomialParameterPoint t)) = _
    rw [s2e_u1_projectiveChartCurve_point]
    change Point.map ℓ = (fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg
      ((s2e_finiteDimensionalProjectivePointEquiv (V := H) k hd).symm R)) at hℓ
    rw [hℓ]
    dsimp only
    rw [s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
    congr 2
    exact (congrArg e.symm (s2e_u1_projectiveChartLine_coordinates.{0, 0} i φ t)).trans htv
  have hk := s2e_u1_canonical_line_kernel Z B (2 * k) γ hsurj hγ hquot hg θ δ hθ b hline
    (fun U hU => s2e_u1_polynomialCurve_regular_sections B f U hU)
    (fun U hU a => s2e_u1_polynomialCurve_stationary B f hstationary U hU a)
  apply s2e_u1_projective_chart_constant_of_scalar_variation i φ
  obtain ⟨a, ha⟩ := hk.1
  refine ⟨a, ?_⟩
  have he := congrArg e ha
  simpa [θ, δ, v, w] using he

end HodgeLean.Foundations.Program
