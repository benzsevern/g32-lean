import HodgeLean.Foundations.Program.SchoenCyclePairedLineKernel
import HodgeLean.Foundations.Program.SchoenCyclePairedLiftContinuity
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectivePolynomialCurve
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveLineCoordinates
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveScalarKernel
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialCurveStationary

/-! # Stationary paired curves in projective charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace Filter Topology
open HodgeLean.Adapters
open scoped BigOperators ContDiff
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

theorem s2e_paired_projectiveChart_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R))
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
  let H := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)
  let b := Module.finBasisOfFinrankEq ℂ H hd
  let e := b.equivFun
  let v : CoordinateSpace k := fun j => (φ (chartCoordinate i j)).fst
  let δ : CoordinateSpace k := fun j => (φ (chartCoordinate i j)).snd
  have hv (t : ℂ) : v + t • δ ≠ 0 := by
    rw [← s2e_u1_projectiveChartLine_coordinates.{0, 0} i φ t]
    exact vectorOfAwayRingHom_ne_zero i _
  have hv0 : v ≠ 0 := by simpa only [zero_smul, add_zero] using hv 0
  have ha : (∑ j, v j • b j) ≠ 0 := by
    rw [← Module.Basis.equivFun_symm_apply]
    exact e.symm.map_ne_zero_iff.mpr hv0
  let A : (Fin (k + 1) → ℂ) → ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :=
    fun t => if h : v + t ≠ 0 then vectorToComplexPoint (v + t) h
      else vectorToComplexPoint v hv0
  have hA :
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := H) k hd
      ∀ᶠ t in 𝓝 0, ∃ ht : (∑ j, (v + t) j • b j) ≠ 0,
        A t = ep (Projectivization.mk ℂ (∑ j, (v + t) j • b j) ht) := by
    have hn : ∀ᶠ t : Fin (k + 1) → ℂ in 𝓝 0, v + t ≠ 0 :=
      (show ContinuousAt (fun t : Fin (k + 1) → ℂ => v + t) 0 from
        continuousAt_const.add continuousAt_id).eventually_ne
          (by change v + 0 ≠ 0; simpa only [add_zero] using hv0)
    filter_upwards [hn] with t ht
    have hsum : (∑ j, (v + t) j • b j) ≠ 0 := by
      rw [← Module.Basis.equivFun_symm_apply]
      exact e.symm.map_ne_zero_iff.mpr ht
    refine ⟨hsum, ?_⟩
    dsimp only [A]
    rw [dif_pos ht]
    apply (s2e_finiteDimensionalProjectivePointEquiv (V := H) k hd).symm.injective
    rw [Equiv.symm_apply_apply, s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
    congr 1
    exact Module.Basis.equivFun_symm_apply b (v + t)
  let f := s2e_u1_projectiveChartCurve i φ ≫ ℓ
  let β : ℂ → ComplexPoint B := fun t => Point.map f (s2e_u1_polynomialParameterPoint t)
  have hline : ∀ᶠ t in 𝓝 (0 : ℂ), β t = Point.map ℓ (A (t • δ)) := by
    apply Filter.Eventually.of_forall
    intro t
    change Point.map ℓ (Point.map (s2e_u1_projectiveChartCurve i φ)
      (s2e_u1_polynomialParameterPoint t)) = _
    rw [s2e_u1_projectiveChartCurve_point]
    dsimp only [A]
    rw [dif_pos (hv t)]
    apply congrArg (Point.map ℓ)
    congr 1
    exact s2e_u1_projectiveChartLine_coordinates.{0, 0} i φ t
  have hβ : ContinuousAt β 0 := by
    have hh := s2e_paired_homogeneous_lift_continuousAt Z B k r hr y hy w hres horder hout
      hgenus hd γ hγ hsurj hquot ℓ hℓ b v ha A hA
    have ht : ContinuousAt (fun t : ℂ => t • δ) 0 := continuousAt_id.smul continuousAt_const
    have hh' := hh.comp_of_eq ht (zero_smul ℂ δ)
    exact hh'.congr (Filter.EventuallyEq.symm hline)
  obtain ⟨α, hα⟩ := s2e_paired_parameter_line_scalar_kernel Z B k r hr y hy w hres
    horder hout hgenus hd γ hγ hsurj hquot ℓ hℓ b v ha A hA δ β hβ hline
    (fun U hU => (s2e_u1_polynomialCurve_regular_sections B f U hU).2)
    (fun U hU c => s2e_u1_polynomialCurve_stationary B f hstationary U hU c)
  apply s2e_u1_projective_chart_constant_of_scalar_variation i φ
  refine ⟨α, ?_⟩
  rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_symm_apply] at hα
  change e.symm δ = α • e.symm v at hα
  have he := congrArg e hα
  simpa only [LinearEquiv.apply_symm_apply, map_smul] using he

end HodgeLean.Foundations.Program
