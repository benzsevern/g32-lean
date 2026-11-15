import HodgeLean.Foundations.Program.CurveJacobianRestHarmLocal

/-! # Track B3, lane Rest: weakly harmonic forms are smooth

The local harmonic representatives of a weakly harmonic `L²` form `h`
(`b3Rest_exists_local_harmonic`) agree on overlaps: two smooth forms with the same pairings
against all forms supported in an open set agree there (`b3Rest_eq_of_inner_eq`, testing against
`χ (β₁ - β₂)` for a bump `χ`). So they glue to a smooth form `α`, closed and coclosed, and a
partition of unity shows `⟨h, φ⟩ = ⟨α, φ⟩` for all smooth `φ`; hence `h = α`
(`b3Rest_weakHarmonic_eq`). This is **Weyl's lemma on the surface**.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- **A smooth bump at `x` supported in an open neighbourhood `W`.** -/
theorem b3Rest_exists_bump_at [T2Space C] (hE : Module.finrank ℂ E = 1) (x : C) {W : Set C}
    (hW : IsOpen W) (hx : x ∈ W) :
    ∃ χ : C → ℝ, b3Rest_SmoothFun (E := E) χ ∧ (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧ χ x = 1 ∧
      tsupport χ ⊆ W := by
  set V := (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' W
  have hVo : IsOpen V := (chartAt E x).continuousOn_symm.isOpen_inter_preimage
    (chartAt E x).open_target hW
  have hxV : chartAt E x x ∈ V := ⟨(chartAt E x).map_source (mem_chart_source E x), by
    show (chartAt E x).symm (chartAt E x x) ∈ W
    rw [(chartAt E x).left_inv (mem_chart_source E x)]; exact hx⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hVo _ hxV
  have he := b3Rest_e_ne_zero hE
  set r := ε / ‖b3Rest_e hE‖
  have hr : 0 < r := div_pos hε (norm_pos_iff.2 he)
  have hζV : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE x z ∈ V := by
    intro z hz
    apply hεV
    rw [mem_ball, dist_eq_norm, b3Rest_ζ, add_sub_cancel_left, norm_smul]
    rwa [lt_div_iff₀ (norm_pos_iff.2 he)] at hz
  obtain ⟨g, hg, hgc, hgs, hg01, hg1⟩ := b3Rest_exists_bump (r₁ := r / 2) (r₂ := r)
    (by positivity) (by linarith)
  have hr' : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE x z ∈ (chartAt E x).target := fun z hz ↦
    (hζV z hz).1
  refine ⟨b3Rest_cfun hE x g, b3Rest_smoothFun_cfun hE x hg hgc fun z hz ↦
    hr' z (mem_ball_zero_iff.1 (hgs hz)), b3Rest_cfun_nonneg hE x hg01, ?_, ?_⟩
  · have h0 := b3Rest_cfun_ζ hE x g (z := 0) (hr' 0 (by simp [hr]))
    have hζ0 : b3Rest_ζ hE x 0 = chartAt E x x := by simp [b3Rest_ζ]
    rw [hζ0, (chartAt E x).left_inv (mem_chart_source E x)] at h0
    rw [h0]
    exact hg1 0 (by simp; positivity)
  · refine (b3Rest_tsupport_cfun_reg hE x hgc hgs hr').trans ?_
    rintro p ⟨hp, z, hz, hzp⟩
    have := (hζV z (mem_ball_zero_iff.1 hz)).2
    rw [hzp] at this
    rwa [mem_preimage, (chartAt E x).left_inv hp] at this

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
  [hE1 : Fact (Module.finrank ℂ E = 1)]

/-- **Two smooth forms with the same pairings against forms supported in an open set agree
there.** -/
theorem b3Rest_eq_of_inner_eq {β₁ β₂ : b3Rest_SF E C} {W : Set C} (hW : IsOpen W)
    (h : ∀ φ : b3Rest_SF E C, tsupport φ.form ⊆ W → inner ℝ β₁ φ = inner ℝ β₂ φ) :
    ∀ x ∈ W, β₁.form x = β₂.form x := by
  have hE := hE1.out
  intro x hx
  by_contra hne
  set γ := β₁ - β₂
  have hγx : γ.form x ≠ 0 := by
    simp only [γ, b3Rest_SF.form_sub, Pi.sub_apply, sub_ne_zero]
    exact hne
  obtain ⟨χ, hχ, h01, hχx, hχW⟩ := b3Rest_exists_bump_at hE x hW hx
  let φ : b3Rest_SF E C := b3Rest_SF.mk (b3Forms_smulFun χ γ.form)
    (b3Forms_IsSmooth.smulFun' hχ γ.isSmooth)
  have hφW : tsupport φ.form ⊆ W := (b3Forms_tsupport_smulFun_subset_left _ _).trans hχW
  have h0 : inner ℝ γ φ = 0 := by rw [inner_sub_left, h φ hφW, sub_self]
  have hpos : 0 < inner ℝ γ φ := by
    rw [b3Rest_SF.inner_def, b3Rest_inner]
    show 0 < b3Forms_integral (b3Rest_b hE)
      (b3Forms_wedgeForm γ.form (b3Forms_star (b3Forms_smulFun χ γ.form)))
    rw [b3Rest_wedgeForm_star_smulFun]
    refine b3Forms_integral_pos _
      (b3Forms_IsSmooth.smulFun' hχ (γ.isSmooth.wedgeForm γ.isSmooth.star))
      (fun x' u hu ↦ ?_) x (fun x' hx' ↦ ?_)
    · rw [b3Forms_loc_smulFun]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [b3Forms_density_wedge_star hE (b3Rest_e_ne_zero hE) γ.form hu]
      exact mul_nonneg (h01 _).1 (by positivity)
    · rw [b3Forms_loc_smulFun]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [(chartAt E x').left_inv hx', hχx, one_mul,
        b3Forms_density_wedge_star hE (b3Rest_e_ne_zero hE) γ.form
          ((chartAt E x').map_source hx')]
      set a := b3Forms_loc γ.form x' (chartAt E x' x) (fun _ ↦ b3Rest_e hE)
      set c := b3Forms_loc γ.form x' (chartAt E x' x) (fun _ ↦ Complex.I • b3Rest_e hE)
      by_contra hle
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
      have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
      exact b3Forms_loc_ne_zero γ.form hx' hγx (b3Forms_eq_zero_of_basis hE (b3Rest_e_ne_zero hE) ha hc)
  linarith

omit [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] hE1 in
/-- Forms agreeing on an open set have eventually equal local representatives there. -/
theorem b3Rest_loc_eventuallyEq {k : ℕ} {γ₁ γ₂ : C → E [⋀^Fin k]→L[ℝ] ℝ} {V : Set C}
    (hV : IsOpen V) (heq : EqOn γ₁ γ₂ V) (x : C) {u : E} (hu : u ∈ (chartAt E x).target)
    (huV : (chartAt E x).symm u ∈ V) : b3Forms_loc γ₁ x =ᶠ[𝓝 u] b3Forms_loc γ₂ x := by
  have hW : (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' V ∈ 𝓝 u :=
    ((chartAt E x).continuousOn_symm.isOpen_inter_preimage (chartAt E x).open_target hV).mem_nhds
      ⟨hu, huV⟩
  filter_upwards [hW] with u' hu'
  simp only [b3Forms_loc, heq hu'.2]

omit [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] hE1 in
/-- The exterior derivative of forms agreeing on an open set agree there. -/
theorem b3Rest_d_eq_of_eqOn {k : ℕ} {γ₁ γ₂ : C → E [⋀^Fin k]→L[ℝ] ℝ} {V : Set C}
    (hV : IsOpen V) (heq : EqOn γ₁ γ₂ V) {p : C} (hp : p ∈ V) :
    b3Forms_d γ₁ p = b3Forms_d γ₂ p := by
  have h := b3Rest_loc_eventuallyEq hV heq p ((chartAt E p).map_source (mem_chart_source E p))
    (by rw [(chartAt E p).left_inv (mem_chart_source E p)]; exact hp)
  exact h.extDeriv_eq

/-- The form of a finite sum. -/
theorem b3Rest_SF.form_sum {ι : Type*} (S : Finset ι) (f : ι → b3Rest_SF E C) :
    (∑ i ∈ S, f i).form = ∑ i ∈ S, (f i).form := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, b3Rest_SF.form_add, ih]

/-- **Weakly harmonic `L²` forms are smooth harmonic forms.** -/
theorem b3Rest_weakHarmonic_eq (h : b3Rest_L2 E C) (hEx : h ∈ (b3Rest_Ex E C)ᗮ)
    (hCo : h ∈ (b3Rest_Co E C)ᗮ) :
    ∃ α : b3Rest_SF E C, b3Forms_d α.form = 0 ∧ b3Forms_d (b3Forms_star α.form) = 0 ∧
      h = (α : b3Rest_L2 E C) := by
  have hE := hE1.out
  choose β U hUo hpU hpair hharm using fun p ↦ b3Rest_exists_local_harmonic h hEx hCo p
  have hcons : ∀ p q, ∀ x ∈ U p ∩ U q, (β p).form x = (β q).form x := by
    intro p q
    refine b3Rest_eq_of_inner_eq ((hUo p).inter (hUo q)) fun φ hφ ↦ ?_
    rw [← UniformSpace.Completion.inner_coe (β p) φ, ← hpair p φ (hφ.trans inter_subset_left),
      hpair q φ (hφ.trans inter_subset_right), UniformSpace.Completion.inner_coe]
  set α₀ : C → E [⋀^Fin 1]→L[ℝ] ℝ := fun p ↦ (β p).form p
  have hloc : ∀ p, ∀ p' ∈ U p, α₀ p' = (β p).form p' := fun p p' hp' ↦
    hcons p' p p' ⟨hpU p', hp'⟩
  -- near each point the glued form is a local representative
  have hev : ∀ (x p : C), ∀ u ∈ (chartAt E x).target, (chartAt E x).symm u = p →
      b3Forms_loc α₀ x =ᶠ[𝓝 u] b3Forms_loc (β p).form x := by
    intro x p u hu hup
    have hV : (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' U p ∈ 𝓝 u :=
      ((chartAt E x).continuousOn_symm.isOpen_inter_preimage (chartAt E x).open_target
        (hUo p)).mem_nhds ⟨hu, by rw [mem_preimage, hup]; exact hpU p⟩
    filter_upwards [hV] with u' hu'
    simp only [b3Forms_loc, hloc p _ hu'.2]
  have hsm : b3Forms_IsSmooth α₀ := by
    intro x
    refine contDiffOn_of_locally_contDiffOn fun u hu ↦ ?_
    set p := (chartAt E x).symm u
    refine ⟨(chartAt E x).target ∩ (chartAt E x).symm ⁻¹' U p,
      (chartAt E x).continuousOn_symm.isOpen_inter_preimage (chartAt E x).open_target (hUo p),
      ⟨hu, hpU p⟩, ?_⟩
    refine ((β p).isSmooth x).mono inter_subset_left |>.congr fun u' hu' ↦ ?_
    simp only [b3Forms_loc, hloc p _ hu'.2.2]
  let α : b3Rest_SF E C := b3Rest_SF.mk α₀ hsm
  have heqOn : ∀ p, EqOn α₀ (β p).form (U p) := fun p p' hp' ↦ hloc p p' hp'
  have heqOn' : ∀ p, EqOn (b3Forms_star α₀) (b3Forms_star (β p).form) (U p) := fun p p' hp' ↦ by
    simp only [b3Forms_star, hloc p p' hp']
  refine ⟨α, ?_, ?_, ?_⟩
  · funext p
    rw [b3Rest_SF.form_mk, b3Rest_d_eq_of_eqOn (hUo p) (heqOn p) (hpU p)]
    exact (hharm p p (hpU p)).1
  · funext p
    rw [b3Rest_SF.form_mk, b3Rest_d_eq_of_eqOn (hUo p) (heqOn' p) (hpU p)]
    exact (hharm p p (hpU p)).2
  -- the pairings agree, by a partition of unity
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ U hUo
    (fun x _ ↦ mem_iUnion.2 ⟨x, hpU x⟩)
  set S := (ρ.locallyFinite.finite_nonempty_of_compact).toFinset
  have hρ0 : ∀ i ∉ S, ∀ z, ρ i z = 0 := by
    intro i hi z
    by_contra hz
    exact hi ((Set.Finite.mem_toFinset _).2 ⟨z, hz⟩)
  have hsum : ∀ z, ∑ i ∈ S, ρ i z = 1 := by
    intro z
    rw [← ρ.sum_eq_one (mem_univ z)]
    refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).symm
    by_contra h'
    exact hi (hρ0 i h' z)
  have hall : ∀ φ : b3Rest_SF E C, inner ℝ h (φ : b3Rest_L2 E C) = inner ℝ (α : b3Rest_L2 E C) φ := by
    intro φ
    let piece : C → b3Rest_SF E C := fun i ↦
      b3Rest_SF.mk (b3Forms_smulFun (ρ i) φ.form) (φ.isSmooth.smulFun (ρ i).contMDiff)
    have hφsum : φ = ∑ i ∈ S, piece i := by
      refine b3Rest_SF.ext ?_
      rw [b3Rest_SF.form_sum]
      funext z
      simp only [piece, b3Rest_SF.form_mk, Finset.sum_apply, b3Forms_smulFun, ← Finset.sum_smul,
        hsum, one_smul]
    have hcoe : ((φ : b3Rest_SF E C) : b3Rest_L2 E C) = ∑ i ∈ S, ((piece i : b3Rest_SF E C) : b3Rest_L2 E C) := by
      conv_lhs => rw [hφsum]
      exact map_sum (UniformSpace.Completion.toCompl (α := b3Rest_SF E C)) _ _
    rw [hcoe, inner_sum, inner_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsupp : tsupport (piece i).form ⊆ U i :=
      (b3Forms_tsupport_smulFun_subset_left _ _).trans (hρ i)
    rw [hpair i (piece i) hsupp, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, b3Rest_SF.inner_def, b3Rest_SF.inner_def, b3Rest_inner,
      b3Rest_inner]
    congr 1
    funext z
    by_cases hz : z ∈ U i
    · have hα : α.form z = (β i).form z := hloc i z hz
      simp only [b3Forms_wedgeForm, hα]
    · have hz0 : (piece i).form z = 0 := by
        have : z ∉ tsupport (ρ i) := fun h' ↦ hz (hρ i h')
        simp [piece, b3Forms_smulFun, image_eq_zero_of_notMem_tsupport this]
      rw [b3Rest_wedge_star_eq_zero hz0, b3Rest_wedge_star_eq_zero hz0]
  -- density
  set v := h - (α : b3Rest_L2 E C)
  have hv : ∀ w : b3Rest_L2 E C, inner ℝ v w = 0 := by
    intro w
    induction w using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
    | ih φ => rw [inner_sub_left, hall φ, sub_self]
  have := hv v
  rw [inner_self_eq_zero, sub_eq_zero] at this
  exact this

end HodgeLean.Foundations.Program
