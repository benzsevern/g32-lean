import HodgeLean.Foundations.Program.SchoenCycleNativeParameterEvaluation

/-! # Scalar factors of one-dimensional chart lines -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A complex linear line in the one-dimensional coordinate space has a
single scalar factor.
Source: Mathlib, LinearMap.map_smul. -/
theorem s2e_one_dimensional_line_apply
    (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) (z : ℂ) :
    (L z) 0 = (L 1) 0 * z := by
  have h : L z = z • L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul z (1 : ℂ)
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- A coordinate line equivalence has nonzero scalar factor.
Source: Mathlib, LinearEquiv.injective. -/
theorem s2e_one_dimensional_line_scale_ne_zero
    (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) : (L 1) 0 ≠ 0 := by
  intro h
  have hv : L 1 = 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, Pi.zero_apply] using h
  have hz : (1 : ℂ) = 0 := L.injective (hv.trans L.map_zero.symm)
  exact one_ne_zero hz

/-- The actual linear chart line rescales the centered coordinate by its
nonzero scalar factor.
Source: Mathlib, OpenPartialHomeomorph.right_inv and ContinuousLinearEquiv.continuous. -/
theorem s2e_centered_chart_evaluation_linear
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (p : M) (hp : p ∈ e.source) (f : M → ℂ)
    (hf : ∀ q ∈ e.source, f q = e q 0 - e p 0)
    (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    (fun z : ℂ => f (e.symm (e p + L z))) =ᶠ[nhds 0]
      (fun z => (L 1) 0 * z) := by
  have hcont : Continuous (fun z : ℂ => e p + L z) := continuous_const.add L.continuous
  have ht : ∀ᶠ z : ℂ in nhds 0, e p + L z ∈ e.target := by
    have hT : Filter.Tendsto (fun z : ℂ => e p + L z) (nhds 0) (nhds (e p)) := by
      simpa only [map_zero, add_zero] using hcont.tendsto (0 : ℂ)
    exact hT (e.open_target.mem_nhds (e.map_source hp))
  filter_upwards [ht] with z hz
  rw [hf _ (e.symm.map_source hz), e.right_inv hz]
  simpa only [Pi.add_apply, add_sub_cancel_left] using s2e_one_dimensional_line_apply L z

/-- A native regular germ has a section representative evaluating to the
specified line's scalar multiple near the chart origin.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; Mathlib,
OpenPartialHomeomorph.right_inv. -/
theorem s2e_native_curve_parameter_linear_chart
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X)
    (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    ∃ (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)),
      X.left.presheaf.germ U p.underlying hp s = s2e_native_curve_parameter X p ∧
      (L 1) 0 ≠ 0 ∧
      (fun z : ℂ => Point.evaluate U s
        ((ComplexPoint.localChart X 1 p).symm
          (ComplexPoint.localChart X 1 p p + L z))) =ᶠ[nhds 0]
        (fun z => (L 1) 0 * z) := by
  obtain ⟨U, hp, s, hs, hf⟩ := s2e_native_curve_parameter_regular_chart X p
  refine ⟨U, hp, s, hs, s2e_one_dimensional_line_scale_ne_zero L, ?_⟩
  exact s2e_centered_chart_evaluation_linear (ComplexPoint.localChart X 1 p) p
    (ComplexPoint.mem_localChart_source X 1 p) (Point.evaluate U s) hf L

end HodgeLean.Foundations.Program
