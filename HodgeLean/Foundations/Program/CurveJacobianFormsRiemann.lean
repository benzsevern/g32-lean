import HodgeLean.Foundations.Program.CurveJacobianFormsStokes

/-!
# Track B3 foundations: a Riemann surface as an oriented real surface

A complex manifold `C` modelled on a complex space `E` (`IsManifold 𝓘(ℂ, E) ω C`, the setting of
`CurveJacobianDefs.lean`) is a smooth real manifold for the same charts
(`b3Forms_isManifold_real`), and its atlas is oriented (`b3Forms_oriented_complex`): the real
Jacobian of a holomorphic change of coordinates is `|det_ℂ|² > 0`. So the forms, integrals and
Stokes' theorem of the `CurveJacobianForms…` files apply to compact Riemann surfaces.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type*} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **A complex manifold is a smooth real manifold** for the same charts. -/
theorem b3Forms_isManifold_real : IsManifold 𝓘(ℝ, E) ∞ C :=
  isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ by
    have h := HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ, E)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
    have := (h.1.restrict_scalars ℝ).of_le (m := ∞) le_top
    simpa using this

attribute [local instance] b3Forms_isManifold_real

/-- Changes of coordinates of a complex manifold are holomorphic. -/
theorem b3Forms_contDiffOn_tr_complex (x y : C) :
    ContDiffOn ℂ ω (b3Forms_tr (E := E) x y) (b3Forms_trDom x y) := by
  have := contDiffOn_ext_coord_change (I := 𝓘(ℂ, E)) (n := ω) y x
  simpa [b3Forms_tr, b3Forms_trDom, extChartAt, PartialEquiv.trans_source, Function.comp_def]
    using this

theorem b3Forms_differentiableAt_tr_complex {x y : C} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    DifferentiableAt ℂ (b3Forms_tr (E := E) x y) u :=
  ((b3Forms_contDiffOn_tr_complex x y).contDiffAt
    ((b3Forms_isOpen_trDom x y).mem_nhds hu)).differentiableAt (by simp)

/-- The complex derivative of a change of coordinates is invertible. -/
theorem b3Forms_det_fderiv_tr_complex_ne_zero [FiniteDimensional ℂ E] {x y : C} {u : E}
    (hu : u ∈ b3Forms_trDom x y) :
    LinearMap.det (fderiv ℂ (b3Forms_tr (E := E) x y) u : E →ₗ[ℂ] E) ≠ 0 := by
  have hw : b3Forms_tr (E := E) x y u ∈ b3Forms_trDom y x :=
    ⟨b3Forms_tr_mem_target hu, by
      rw [mem_preimage, b3Forms_symm_tr hu]; exact (chartAt E x).map_target hu.1⟩
  have h1 : b3Forms_tr (E := E) y x ∘ b3Forms_tr x y =ᶠ[𝓝 u] id := by
    filter_upwards [(b3Forms_isOpen_trDom x y).mem_nhds hu] with v hv
    simp only [Function.comp_apply, b3Forms_tr, id]
    rw [(chartAt E y).left_inv hv.2, (chartAt E x).right_inv hv.1]
  have h2 := fderiv_comp u (b3Forms_differentiableAt_tr_complex hw)
    (b3Forms_differentiableAt_tr_complex hu)
  rw [h1.fderiv_eq, fderiv_id] at h2
  intro h0
  have key : (fderiv ℂ (b3Forms_tr (E := E) y x) (b3Forms_tr x y u) : E →ₗ[ℂ] E) ∘ₗ
      (fderiv ℂ (b3Forms_tr (E := E) x y) u : E →ₗ[ℂ] E) = LinearMap.id := by
    ext v
    exact congrArg (fun L : E →L[ℂ] E ↦ L v) h2.symm
  have := congrArg LinearMap.det key
  rw [LinearMap.det_comp, h0, mul_zero, LinearMap.det_id] at this
  exact zero_ne_one this

/-- **The atlas of a Riemann surface is oriented**: the real Jacobian of a holomorphic change of
coordinates is the squared modulus of its complex Jacobian. -/
theorem b3Forms_oriented_complex [FiniteDimensional ℂ E] : b3Forms_Oriented E C := by
  intro x y u hu
  have hR := (b3Forms_differentiableAt_tr_complex hu).fderiv_restrictScalars ℝ
  rw [hR]
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (b3Forms_tr (E := E) x y) u) :
      E →L[ℝ] E) : E →ₗ[ℝ] E) =
      LinearMap.restrictScalars ℝ (fderiv ℂ (b3Forms_tr (E := E) x y) u : E →ₗ[ℂ] E) := rfl
  rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.2 (b3Forms_det_fderiv_tr_complex_ne_zero hu)

end HodgeLean.Foundations.Program
