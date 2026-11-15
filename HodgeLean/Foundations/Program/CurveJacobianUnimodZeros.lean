import HodgeLean.Foundations.Program.CurveJacobianRestChart
import HodgeLean.Foundations.Program.CurveJacobianAExact

/-! # Track B3, lane Unimod: the zeros of a holomorphic form

* the coordinate functional `κ : E → ℂ` of the model line, `w = κ w • e` (`b3Unimod_κ_spec`), and
  the inverse of the real coordinate `b3Rest_L` is `κ`;
* `b3Unimod_Z θ`, the points where `θ` vanishes; in a chart it is the zero set of the coefficient
  of `θ` (`b3Unimod_coef_eq_zero_iff`);
* `b3Unimod_Z_finite`: a nonzero holomorphic form on a compact connected Riemann surface has
  finitely many zeros. Near each point the disc coefficient is analytic, so the zeros either fill
  a neighbourhood or are isolated; the points of the first kind form a clopen set, which is empty
  since `θ ≠ 0`, and a compact set of isolated points is finite.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

section Coord

variable (hE : Module.finrank ℂ E = 1)

/-- The coordinate functional of the model line, `κ (c • e) = c`. -/
def b3Unimod_κ : E →L[ℂ] ℂ :=
  ((b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).symm : E →L[ℂ] ℂ)

theorem b3Unimod_κ_spec (w : E) : w = b3Unimod_κ hE w • b3Rest_e hE := by
  have := (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).apply_symm_apply w
  rw [b3Forms_lineEquiv_apply] at this
  exact this.symm

theorem b3Unimod_κ_e : b3Unimod_κ hE (b3Rest_e hE) = 1 := by
  have := (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).symm_apply_apply 1
  rw [b3Forms_lineEquiv_apply, one_smul] at this
  exact this

theorem b3Unimod_L_symm (w : E) : (b3Rest_L hE).symm w = b3Unimod_κ hE w := rfl

theorem b3Unimod_κ_smul_e (c : ℂ) : b3Unimod_κ hE (c • b3Rest_e hE) = c := by
  rw [map_smul, b3Unimod_κ_e, smul_eq_mul, mul_one]

/-- The complex coordinate centred at `q` of the chart at `q`. -/
def b3Unimod_ζ (q : C) (y : C) : ℂ := b3Unimod_κ hE (chartAt E q y - chartAt E q q)

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_disc_ζ {q y : C} (hy : y ∈ (chartAt E q).source) :
    b3A_disc q (b3Rest_e hE) (b3Unimod_ζ hE q y) = y := by
  rw [b3A_disc, b3Unimod_ζ, ← b3Unimod_κ_spec, add_sub_cancel]
  exact (chartAt E q).left_inv hy

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_ζ_self (q : C) : b3Unimod_ζ hE q q = 0 := by
  simp [b3Unimod_ζ]

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_continuousOn_ζ (q : C) :
    ContinuousOn (b3Unimod_ζ hE q) (chartAt E q).source :=
  ((b3Unimod_κ hE).continuous.comp (continuous_id.sub continuous_const)).comp_continuousOn
    (chartAt E q).continuousOn

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_ζ_injOn (q : C) : InjOn (b3Unimod_ζ hE q) (chartAt E q).source := by
  intro y hy y' hy' h
  have h1 := b3Unimod_disc_ζ hE hy
  rw [h, b3Unimod_disc_ζ hE hy'] at h1
  exact h1.symm

end Coord

section Zeros

/-- **The zeros of a holomorphic form.** -/
def b3Unimod_Z (θ : b3_HolForm E C) : Set C :=
  {y | ∀ v : TangentSpace 𝓘(ℂ, E) y, θ.1 ⟨y, v⟩ = 0}

variable (hE : Module.finrank ℂ E = 1)
include hE

theorem b3Unimod_coef_eq_zero_iff (θ : b3_HolForm E C) {x y : C}
    (hy : y ∈ (chartAt E x).source) :
    b3A_coef θ.1 x (b3Rest_e hE) y = 0 ↔ y ∈ b3Unimod_Z θ := by
  constructor
  · intro h v
    rw [b3A_holForm_apply_eq θ.2 (b3Unimod_κ hE) (b3Rest_e hE) (b3Unimod_κ_spec hE) x ⟨y, v⟩ hy,
      h, mul_zero]
  · intro h
    exact h _

/-- Near each point, the zeros of `θ` fill a neighbourhood or are isolated. -/
theorem b3Unimod_Z_local (θ : b3_HolForm E C) (q : C) :
    (∀ᶠ y in 𝓝 q, y ∈ b3Unimod_Z θ) ∨ ∀ᶠ y in 𝓝[≠] q, y ∉ b3Unimod_Z θ := by
  set u := b3Rest_e hE
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u (b3Rest_e_ne_zero hE) q
  set g := b3A_discCoef θ.1 q u
  have hd : DifferentiableOn ℂ g (Metric.ball 0 R) := fun z hz ↦
    (b3A_discCoef_differentiableAt θ.2 q u (hR z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
  have han : AnalyticAt ℂ g 0 := hd.analyticAt (Metric.ball_mem_nhds 0 hR0)
  have hsrc : (chartAt E q).source ∈ 𝓝 q :=
    (chartAt E q).open_source.mem_nhds (mem_chart_source E q)
  have hζ : Tendsto (b3Unimod_ζ hE q) (𝓝 q) (𝓝 0) := by
    have := ((b3Unimod_continuousOn_ζ hE q).continuousAt hsrc).tendsto
    rwa [b3Unimod_ζ_self] at this
  have hgζ : ∀ y ∈ (chartAt E q).source, g (b3Unimod_ζ hE q y) = b3A_coef θ.1 q u y := by
    intro y hy
    simp only [g, b3A_discCoef]
    rw [b3Unimod_disc_ζ hE hy]
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · left
    filter_upwards [hζ.eventually h, hsrc] with y hy hys
    rw [hgζ y hys] at hy
    exact (b3Unimod_coef_eq_zero_iff hE θ hys).1 hy
  · right
    have hζ' : Tendsto (b3Unimod_ζ hE q) (𝓝[≠] q) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hζ.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [nhdsWithin_le_nhds hsrc, self_mem_nhdsWithin] with y hys hyq
      intro h0
      apply hyq
      exact b3Unimod_ζ_injOn hE q hys (mem_chart_source E q) (by rw [h0, b3Unimod_ζ_self])
    filter_upwards [hζ'.eventually h, nhdsWithin_le_nhds hsrc] with y hy hys
    rw [hgζ y hys] at hy
    exact fun h' ↦ hy ((b3Unimod_coef_eq_zero_iff hE θ hys).2 h')

/-- **The zeros of a nonzero holomorphic form are finite** on a compact connected surface. -/
theorem b3Unimod_Z_finite [CompactSpace C] [ConnectedSpace C] {θ : b3_HolForm E C}
    (hθ : θ ≠ 0) : (b3Unimod_Z θ).Finite := by
  set Z := b3Unimod_Z θ
  set A := {q : C | ∀ᶠ y in 𝓝 q, y ∈ Z}
  have hAZ : A ⊆ Z := fun q hq ↦ hq.self_of_nhds
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro q hq
    rcases b3Unimod_Z_local hE θ q with h | h
    · exact absurd h hq
    · rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with y hy
      by_cases hyq : y = q
      · rw [hyq]; exact hq
      · exact fun hyA ↦ hy hyq (hAZ hyA)
  have hA : A = ∅ := by
    rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h | h
    · exact h
    · exfalso
      apply hθ
      ext ⟨y, v⟩
      have : y ∈ Z := hAZ (h ▸ mem_univ y)
      exact this v
  have hiso : ∀ q, ∀ᶠ y in 𝓝 q, y ≠ q → y ∉ Z := fun q ↦ by
    rcases b3Unimod_Z_local hE θ q with h | h
    · exact absurd (show q ∈ A from h) (hA ▸ notMem_empty q)
    · exact eventually_nhdsWithin_iff.1 h
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro q hq
    have hsrc : (chartAt E q).source ∈ 𝓝 q :=
      (chartAt E q).open_source.mem_nhds (mem_chart_source E q)
    have hne : b3A_coef θ.1 q (b3Rest_e hE) q ≠ 0 := fun h ↦
      hq ((b3Unimod_coef_eq_zero_iff hE θ (mem_chart_source E q)).1 h)
    have hc := (b3A_coef_contMDiffAt θ.2 q (b3Rest_e hE) (mem_chart_source E q)).continuousAt
    filter_upwards [hc.eventually_ne hne, hsrc] with y hy hys
    exact fun h ↦ hy ((b3Unimod_coef_eq_zero_iff hE θ hys).2 h)
  obtain ⟨t, -, ht⟩ := hZc.isCompact.elim_nhds_subcover (fun q ↦ {y | y ≠ q → y ∉ Z})
    fun q _ ↦ hiso q
  refine t.finite_toSet.subset fun z hz ↦ ?_
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (ht hz)
  by_cases h : z = x
  · rw [h]; exact hx
  · exact absurd hz (hzx h)

end Zeros

end HodgeLean.Foundations.Program
