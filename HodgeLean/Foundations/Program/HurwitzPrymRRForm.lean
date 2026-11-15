import HodgeLean.Foundations.Program.HurwitzPrymCovDegree
import HodgeLean.Foundations.Program.HurwitzPrymCovDescent

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rr`: orders of `1`-forms and of their pullbacks

For a fibrewise linear function `θ` on the tangent bundle of a Riemann surface, the coefficient
in the line coordinate centred at `y` is `HurwitzPrymRR_loc θ y`; its meromorphic order at `0` is
the order of `θ` at `y`. The order does not depend on the chart: in the chart at `y₀` it is the
order of the coefficient at the coordinate of `y`. Along a holomorphic map with ramification index
`e` at `x`, the coefficient of `f^*θ` is `a(T τ) T'(τ)` with `T` of order `e`, so
`ord_x f^*θ = e · ord_{f x} θ + e - 1`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Pull

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- **Fibrewise linear functions on the tangent bundle**, the condition on a `1`-form apart from
regularity.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (differential forms are sections of
the cotangent bundle); Mathlib `TangentBundle`. -/
def HurwitzPrymRR_IsLinear (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) : Prop :=
  ∀ (y : Y) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, E') y), θ ⟨y, a • v + w⟩ = a * θ ⟨y, v⟩ + θ ⟨y, w⟩

omit [IsManifold 𝓘(ℂ, E') ω Y] in
example : HurwitzPrymRR_IsLinear (0 : TangentBundle 𝓘(ℂ, E') Y → ℂ) := fun _ _ _ _ ↦ by simp

omit [IsManifold 𝓘(ℂ, E') ω Y] in
theorem HurwitzPrymRR_IsLinear.smul {θ : TangentBundle 𝓘(ℂ, E') Y → ℂ}
    (hθ : HurwitzPrymRR_IsLinear θ) (y : Y) (a : ℂ) (v : TangentSpace 𝓘(ℂ, E') y) :
    θ ⟨y, a • v⟩ = a * θ ⟨y, v⟩ := by
  have h0 : θ ⟨y, 0⟩ = 0 := by
    have := hθ y 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have := hθ y a v 0
  rwa [add_zero, h0, add_zero] at this

theorem HurwitzPrymRR_coef_pullback (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x₀ : C) (y₀ : Y)
    (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hθ : HurwitzPrymRR_IsLinear θ) (t : E)
    (ht : t ∈ (extChartAt 𝓘(ℂ, E) x₀).target)
    (hft : f ((extChartAt 𝓘(ℂ, E) x₀).symm t) ∈ (extChartAt 𝓘(ℂ, E') y₀).source) :
    b4cov_coef (b3_pullback E E' f θ) x₀ (b4cov_lineEquiv hE 1) t =
      b4cov_coef θ y₀ (b4cov_lineEquiv hE' 1) (b4cov_expr E E' f x₀ y₀ t) *
        (b4cov_lineEquiv hE').symm
          (fderiv ℂ (b4cov_expr E E' f x₀ y₀) t (b4cov_lineEquiv hE 1)) := by
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  set φ := extChartAt 𝓘(ℂ, E) x₀
  set ψ := extChartAt 𝓘(ℂ, E') y₀
  set x := φ.symm t
  have hxs : x ∈ φ.source := φ.map_target ht
  have hφx : φ x = t := φ.right_inv ht
  set κ := L'.symm (fderiv ℂ (b4cov_expr E E' f x₀ y₀) t (L 1))
  have hdf : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₀ x (L 1)) =
      κ • b4cov_vec y₀ (f x) (L' 1) := by
    rw [← b4cov_vec_triv y₀ (f x) hft (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₀ x (L 1))),
      b4cov_triv_mfderiv f hf x₀ y₀ x hxs hft, b4cov_triv_vec x₀ x hxs, hφx,
      ← b4cov_vec_smul y₀ (f x) hft]
    congr 1
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  have hgen : ∀ (y : Y) (_ : y = f x), θ ⟨y, b4cov_vec y₀ y (L' 1)⟩ =
      θ ⟨f x, b4cov_vec y₀ (f x) (L' 1)⟩ := by
    rintro _ rfl; rfl
  have hψ : ψ.symm (b4cov_expr E E' f x₀ y₀ t) = f x := ψ.left_inv hft
  change θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₀ x (L 1))⟩ =
    θ ⟨ψ.symm (b4cov_expr E E' f x₀ y₀ t), b4cov_vec y₀ _ (L' 1)⟩ * κ
  rw [hgen _ hψ, hdf, hθ.smul, mul_comm]


/-- **The coefficient of `θ` in the line coordinate `τ` centred at `y`**: `τ ↦ θ(∂)` at the point
with chart coordinate `φ_y y + L τ`, for the fixed identification `L : ℂ ≃ E'`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9.4 (a `1`-form is `f dz` in a chart);
the coefficient `b4cov_coef`. -/
def HurwitzPrymRR_loc (hE' : Module.finrank ℂ E' = 1) (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ)
    (y : Y) : ℂ → ℂ :=
  fun τ ↦ b4cov_coef θ y (b4cov_lineEquiv hE' 1)
    (extChartAt 𝓘(ℂ, E') y y + b4cov_lineEquiv hE' τ)

example (hE' : Module.finrank ℂ E' = 1) (y : Y) :
    HurwitzPrymRR_loc hE' (0 : TangentBundle 𝓘(ℂ, E') Y → ℂ) y = 0 := rfl

/-- **Pullback in line coordinates.** Near `0`, the coefficient of `f^*θ` at `x₀` is
`a (σ₀ + T τ) · T' τ`, where `a` is the coefficient of `θ` at `y₀`, `T` the transported chart
expression of `f` and `σ₀` the line coordinate of `f x₀` at `y₀`. -/
theorem HurwitzPrymRR_loc_pullback (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x₀ : C) (y₀ : Y)
    (hx₀ : f x₀ ∈ (extChartAt 𝓘(ℂ, E') y₀).source)
    (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hθ : HurwitzPrymRR_IsLinear θ) :
    HurwitzPrymRR_loc hE (b3_pullback E E' f θ) x₀ =ᶠ[𝓝 0]
      (fun τ ↦ HurwitzPrymRR_loc hE' θ y₀
        ((b4cov_lineEquiv hE').symm (extChartAt 𝓘(ℂ, E') y₀ (f x₀) -
          extChartAt 𝓘(ℂ, E') y₀ y₀) +
          b4cov_transport hE hE' (b4cov_expr E E' f x₀ y₀) (extChartAt 𝓘(ℂ, E) x₀ x₀) τ) *
        deriv (b4cov_transport hE hE' (b4cov_expr E E' f x₀ y₀)
          (extChartAt 𝓘(ℂ, E) x₀ x₀)) τ) := by
  set φ := extChartAt 𝓘(ℂ, E) x₀
  set ψ := extChartAt 𝓘(ℂ, E') y₀
  set G := b4cov_expr E E' f x₀ y₀
  have hx₀s : x₀ ∈ φ.source := mem_extChartAt_source x₀
  let T₀ : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)
  have hTo : IsOpen T₀ := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source _))
  have ht₀ : φ x₀ ∈ T₀ := ⟨φ.map_source hx₀s, by
    simp only [mem_preimage, φ.left_inv hx₀s]; exact hx₀⟩
  have hcont : Continuous (fun τ : ℂ ↦ φ x₀ + b4cov_lineEquiv hE τ) :=
    continuous_const.add (b4cov_lineEquiv hE).continuous
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), φ x₀ + b4cov_lineEquiv hE τ ∈ T₀ :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hTo.mem_nhds ht₀)
  filter_upwards [hev] with τ hτ
  have hGd : DifferentiableAt ℂ G (φ x₀ + b4cov_lineEquiv hE τ) :=
    (b4cov_analyticAt_chart f hf x₀ y₀ _ hτ.1 hτ.2).differentiableAt
  have hG0 : G (φ x₀) = ψ (f x₀) := by
    show ψ (f (φ.symm (φ x₀))) = ψ (f x₀)
    rw [φ.left_inv hx₀s]
  rw [b4cov_transport_deriv hE hE' τ hGd]
  simp only [HurwitzPrymRR_loc]
  rw [HurwitzPrymRR_coef_pullback hE hE' f hf x₀ y₀ θ hθ _ hτ.1 hτ.2]
  congr 2
  simp only [b4cov_transport, map_add, map_sub, ContinuousLinearEquiv.apply_symm_apply]
  rw [hG0]
  abel


/-- Multiplying by a unit at `x` does not change the meromorphic order. -/
theorem HurwitzPrymRR_order_mul_unit {F κ : ℂ → ℂ} {x : ℂ} (hκ : AnalyticAt ℂ κ x)
    (hκx : κ x ≠ 0) :
    meromorphicOrderAt (fun τ ↦ F τ * κ τ) x = meromorphicOrderAt F x := by
  have hκo : meromorphicOrderAt κ x = 0 := by
    rw [hκ.meromorphicOrderAt_eq, hκ.analyticOrderAt_eq_zero.2 hκx]
    rfl
  by_cases hF : MeromorphicAt F x
  · rw [show (fun τ ↦ F τ * κ τ) = F * κ from rfl, meromorphicOrderAt_mul hF hκ.meromorphicAt,
      hκo, add_zero]
  · have hFκ : ¬ MeromorphicAt (fun τ ↦ F τ * κ τ) x := by
      intro h
      apply hF
      have h2 := h.mul (hκ.meromorphicAt.inv)
      refine h2.congr ?_
      filter_upwards [nhdsWithin_le_nhds (hκ.continuousAt.eventually_ne hκx)] with τ hτ
      simp [mul_assoc, mul_inv_cancel₀ hτ]
    rw [meromorphicOrderAt_of_not_meromorphicAt hF, meromorphicOrderAt_of_not_meromorphicAt hFκ]

omit [IsManifold 𝓘(ℂ, E') ω Y] in
theorem HurwitzPrymRR_pullback_id (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) :
    b3_pullback E' E' (id : Y → Y) θ = θ := by
  funext p
  simp [b3_pullback, mfderiv_id]

/-- **Orders in a nearby chart**: for `y` in the chart at `y₀`, the order of `θ` at `y` is the
order of the coefficient at `y₀` at the line coordinate of `y`. -/
theorem HurwitzPrymRR_ord_chart (hE' : Module.finrank ℂ E' = 1)
    (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hθ : HurwitzPrymRR_IsLinear θ) (y₀ y : Y)
    (hy : y ∈ (extChartAt 𝓘(ℂ, E') y₀).source) :
    meromorphicOrderAt (HurwitzPrymRR_loc hE' θ y) 0 =
      meromorphicOrderAt (HurwitzPrymRR_loc hE' θ y₀)
        ((b4cov_lineEquiv hE').symm (extChartAt 𝓘(ℂ, E') y₀ y - extChartAt 𝓘(ℂ, E') y₀ y₀)) := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  have : Nontrivial E' := Module.nontrivial_of_finrank_eq_succ hE'
  have hid : ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, E') ω (id : Y → Y) := contMDiff_id
  have h := HurwitzPrymRR_loc_pullback hE' hE' id hid y y₀ hy θ hθ
  rw [HurwitzPrymRR_pullback_id] at h
  set G := b4cov_expr E' E' (id : Y → Y) y y₀
  set T := b4cov_transport hE' hE' G (extChartAt 𝓘(ℂ, E') y y)
  set σ₀ := (b4cov_lineEquiv hE').symm (extChartAt 𝓘(ℂ, E') y₀ (id y) - extChartAt 𝓘(ℂ, E') y₀ y₀)
  have hys : y ∈ (extChartAt 𝓘(ℂ, E') y).source := mem_extChartAt_source y
  have hGan : AnalyticAt ℂ G (extChartAt 𝓘(ℂ, E') y y) :=
    b4cov_analyticAt_chart id hid y y₀ _ ((extChartAt 𝓘(ℂ, E') y).map_source hys)
      (by rw [(extChartAt 𝓘(ℂ, E') y).left_inv hys]; exact hy)
  have hTan : AnalyticAt ℂ T 0 := b4cov_transport_analyticAt hE' hE' hGan
  have hG' : fderiv ℂ G (extChartAt 𝓘(ℂ, E') y y) ≠ 0 := by
    refine (b4cov_mfderiv_ne_zero_iff_expr id hid y y₀ y hys hy).1 ?_
    rw [mfderiv_id]
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : E')
    exact hv (congrArg (fun T : E' →L[ℂ] E' ↦ T v) h0)
  have hT' : deriv T 0 ≠ 0 := by
    rw [b4cov_transport_deriv hE' hE' 0 (by simpa using hGan.differentiableAt)]
    simp only [map_zero, add_zero]
    intro h0
    apply hG'
    ext v
    have h1 : fderiv ℂ G (extChartAt 𝓘(ℂ, E') y y) (b4cov_lineEquiv hE' 1) = 0 := by
      simpa using congrArg (b4cov_lineEquiv hE') h0
    have hv : v = (b4cov_lineEquiv hE').symm v • b4cov_lineEquiv hE' 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
    rw [hv, map_smul, h1, smul_zero]
    rfl
  rw [meromorphicOrderAt_congr (h.filter_mono nhdsWithin_le_nhds),
    HurwitzPrymRR_order_mul_unit hTan.deriv hT']
  have hg : AnalyticAt ℂ (fun τ ↦ σ₀ + T τ) 0 := analyticAt_const.add hTan
  have hg' : deriv (fun τ ↦ σ₀ + T τ) 0 ≠ 0 := by
    rw [deriv_const_add]
    exact hT'
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := HurwitzPrymRR_loc hE' θ y₀) hg hg'
  rw [show (fun τ ↦ HurwitzPrymRR_loc hE' θ y₀ (σ₀ + T τ)) =
    HurwitzPrymRR_loc hE' θ y₀ ∘ (fun τ ↦ σ₀ + T τ) from rfl, hcomp]
  simp only [T, b4cov_transport_zero, add_zero, σ₀, id]



/-- **The order of a pullback**: `ord_x (f^*θ) = e_x · ord_{f x} θ + e_x - 1`. -/
theorem HurwitzPrymRR_ord_pullback [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (x₀ : C)
    (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (hmer : MeromorphicAt (HurwitzPrymRR_loc hE' θ (f x₀)) 0) :
    meromorphicOrderAt (HurwitzPrymRR_loc hE (b3_pullback E E' f θ) x₀) 0 =
      meromorphicOrderAt (HurwitzPrymRR_loc hE' θ (f x₀)) 0 *
          ((b4_ramIndex E E' f x₀ : ℤ) : WithTop ℤ) +
        (((b4_ramIndex E E' f x₀ : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  have h := HurwitzPrymRR_loc_pullback hE hE' f hf x₀ (f x₀) (mem_extChartAt_source _) θ hθ
  set T := b4cov_transport hE hE' (b4cov_expr E E' f x₀ (f x₀)) (extChartAt 𝓘(ℂ, E) x₀ x₀)
  set e := b4_ramIndex E E' f x₀
  simp only [sub_self, map_zero, zero_add] at h
  obtain ⟨he1, hne, hlow⟩ := b4cov_ramIndex_spec f hf hnc x₀
  have hx₀s : x₀ ∈ (extChartAt 𝓘(ℂ, E) x₀).source := mem_extChartAt_source x₀
  have hGan : AnalyticAt ℂ (b4cov_expr E E' f x₀ (f x₀)) (extChartAt 𝓘(ℂ, E) x₀ x₀) :=
    b4cov_analyticAt_chart f hf x₀ (f x₀) _ ((extChartAt 𝓘(ℂ, E) x₀).map_source hx₀s)
      (by rw [(extChartAt 𝓘(ℂ, E) x₀).left_inv hx₀s]; exact mem_extChartAt_source _)
  have hTan : AnalyticAt ℂ T 0 := b4cov_transport_analyticAt hE hE' hGan
  have hT0 : T 0 = 0 := b4cov_transport_zero hE hE' _ _
  have hTo : analyticOrderAt T 0 = e :=
    b4cov_analyticOrderAt_transport hE hE' hGan he1 hlow hne
  have hTo' : analyticOrderAt (fun τ ↦ T τ - T 0) 0 = e := by
    simp only [hT0, sub_zero]; exact hTo
  have hnc' : ¬ Filter.EventuallyConst T (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hTo']
    exact ENat.natCast_ne_top _
  have hdo : analyticOrderAt (deriv T) 0 = (e - 1 : ℕ) := by
    have := hTan.analyticOrderAt_deriv_add_one
    rw [hTo'] at this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (deriv T) 0 = k := by
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (show analyticOrderAt (deriv T) 0 ≠ ⊤ from
        fun htop ↦ by rw [htop, top_add] at this; exact ENat.natCast_ne_top _ this.symm)
      exact ⟨k, hk.symm⟩
    rw [hk] at this ⊢
    have : k + 1 = e := by exact_mod_cast this
    congr 1
    omega
  have hmer0 : MeromorphicAt (HurwitzPrymRR_loc hE' θ (f x₀)) (T 0) := by rw [hT0]; exact hmer
  have hmerT : MeromorphicAt (HurwitzPrymRR_loc hE' θ (f x₀) ∘ T) 0 := hmer0.comp_analyticAt hTan
  rw [meromorphicOrderAt_congr (h.filter_mono nhdsWithin_le_nhds),
    show (fun τ ↦ HurwitzPrymRR_loc hE' θ (f x₀) (T τ) * deriv T τ) =
      (HurwitzPrymRR_loc hE' θ (f x₀) ∘ T) * deriv T from rfl,
    meromorphicOrderAt_mul hmerT hTan.deriv.meromorphicAt,
    hmer0.meromorphicOrderAt_comp hTan hnc', hTo', hTan.deriv.meromorphicOrderAt_eq, hdo, hT0]
  simp only [ENat.map_natCast]
  congr 1
  exact_mod_cast congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) (by omega : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1)

end Pull

end HodgeLean.Foundations.Program
