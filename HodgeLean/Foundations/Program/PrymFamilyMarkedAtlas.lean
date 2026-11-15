import HodgeLean.Foundations.Program.PrymFamilyMarkedDefs

/-! # B6-3g, part 5: complex atlases from holomorphic projections

For a continuous, nowhere locally constant map `F : X → ℙ¹` on a topological space, the charts in
which `F` is holomorphic are pairwise compatible: a transition map `h` satisfies `a₂ ∘ h = a₁`
with `a₁`, `a₂` analytic, so off the isolated critical points of `a₂` it is a local inverse
composed with an analytic map, and at the remaining points it is continuous, hence analytic by
the removable singularity theorem. When these charts cover `X` they form a complex atlas for
which `F`, and every continuous injective `T` with `F ∘ T = F`, are holomorphic.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Filter Topology Set
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- An analytic function of one variable that is not locally constant has a derivative that does
not vanish on a punctured neighbourhood. -/
theorem b63g5_deriv_ne_zero {a : ℂ → ℂ} {p : ℂ} (ha : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ a z)
    (hnc : ¬ ∀ᶠ z in 𝓝 p, a z = a p) : ∀ᶠ z in 𝓝[≠] p, deriv a z ≠ 0 := by
  have hd : AnalyticAt ℂ (deriv a) p := ha.self_of_nhds.deriv
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with h0 | h
  · exfalso
    apply hnc
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h0.and ha)
    have hdiff : DifferentiableOn ℂ a (Metric.ball p r) := fun z hz ↦
      (hball z hz).2.differentiableAt.differentiableWithinAt
    filter_upwards [Metric.ball_mem_nhds p hr] with z hz
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball p r).isPreconnected hdiff
      (fun y hy ↦ (hball y hy).1) hz (Metric.mem_ball_self hr)
  · exact h

/-- **Removable comparison.** If `a₂ ∘ h = a₁` near `w`, with `a₁` analytic near `w`, `a₂`
analytic and not locally constant near `h w`, and `h` continuous and injective near `w`, then `h`
is analytic at `w`: off the isolated critical points of `a₂` it is a local inverse of `a₂`
composed with `a₁`, and the remaining point is a removable singularity. -/
theorem b63g5_analyticAt_of_comp {h a₁ a₂ : ℂ → ℂ} {w : ℂ}
    (hc : ∀ᶠ z in 𝓝 w, ContinuousAt h z) (hinj : ∃ N ∈ 𝓝 w, InjOn h N)
    (ha₁ : ∀ᶠ z in 𝓝 w, AnalyticAt ℂ a₁ z) (ha₂ : ∀ᶠ z in 𝓝 (h w), AnalyticAt ℂ a₂ z)
    (hnc : ¬ ∀ᶠ z in 𝓝 (h w), a₂ z = a₂ (h w)) (heq : ∀ᶠ z in 𝓝 w, a₂ (h z) = a₁ z) :
    AnalyticAt ℂ h w := by
  have hcw : ContinuousAt h w := hc.self_of_nhds
  obtain ⟨N, hN, hNinj⟩ := hinj
  -- the critical points of `a₂` are isolated
  have hcrit := b63g5_deriv_ne_zero ha₂ hnc
  -- pull back to a punctured neighbourhood of `w`
  have hne : ∀ᶠ z in 𝓝[≠] w, h z ≠ h w := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hN, self_mem_nhdsWithin] with z hz hzw
    exact fun e ↦ hzw (hNinj hz (mem_of_mem_nhds hN) e)
  have htend : Tendsto h (𝓝[≠] w) (𝓝[≠] (h w)) :=
    tendsto_nhdsWithin_iff.2 ⟨hcw.tendsto.mono_left nhdsWithin_le_nhds, hne⟩
  have hcrit' : ∀ᶠ z in 𝓝[≠] w, deriv a₂ (h z) ≠ 0 := htend.eventually hcrit
  have ha₂' : ∀ᶠ z in 𝓝 w, ∀ᶠ y in 𝓝 (h z), AnalyticAt ℂ a₂ y :=
    hcw.eventually (eventually_eventually_nhds.2 ha₂)
  have hdiff : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ h z := by
    filter_upwards [hcrit', eventually_nhdsWithin_of_eventually_nhds
      ((eventually_eventually_nhds.2 heq).and ((eventually_eventually_nhds.2 hc).and
        (ha₂'.and (eventually_eventually_nhds.2 ha₁))))] with z hz ⟨heqz, hcz, ha₂z, ha₁z⟩
    have hs : HasStrictDerivAt a₂ (deriv a₂ (h z)) (h z) :=
      ha₂z.self_of_nhds.hasStrictDerivAt
    set L := hs.localInverse a₂ (deriv a₂ (h z)) (h z) hz
    have hL : DifferentiableAt ℂ L (a₂ (h z)) :=
      (hs.to_localInverse hz).hasDerivAt.differentiableAt
    have hleft := hcz.self_of_nhds.eventually (hs.eventually_left_inverse hz)
    have hcomp : DifferentiableAt ℂ (L ∘ a₁) z := by
      apply DifferentiableAt.comp
      · rw [← heqz.self_of_nhds]; exact hL
      · exact ha₁z.self_of_nhds.differentiableAt
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hleft, heqz] with y hy hy'
    simp only [Function.comp_apply, ← hy']
    exact hy.symm
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcw

/-- A holomorphic map from an open set of the plane to the sphere is analytic, near each point
of the set, in any sphere chart containing the image of that point. -/
theorem b63g5_analyticAt_chart_comp {g : ℂ → OnePoint ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hg : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g s) {z : ℂ} (hz : z ∈ s) (y : OnePoint ℂ)
    (hy : g z ∈ (chartAt ℂ y).source) :
    ∀ᶠ z' in 𝓝 z, AnalyticAt ℂ (chartAt ℂ y ∘ g) z' := by
  have hgc : ContinuousAt g z := (hg.continuousOn.continuousAt (hs.mem_nhds hz))
  filter_upwards [hs.mem_nhds hz, hgc.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hy)]
    with z' hz' hy'
  have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g z' := hg.contMDiffAt (hs.mem_nhds hz')
  have h2 := ((contMDiffAt_iff_of_mem_source (x := z') (y := y)
    (mem_chart_source ℂ z') hy').1 h1).2
  rw [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    extChartAt_coe, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h2
  exact h2.analyticAt


section Atlas

variable {X : Type} [TopologicalSpace X]

/-- **Comparison of two charts in which `F` is holomorphic.** If `F` is not locally constant,
`φ` and `φ'` are charts in which `F` is holomorphic, and `T` is a continuous injective map with
`F ∘ T = F`, then `T` written in the charts is analytic. -/
theorem b63g5_written_analyticAt (F : X → OnePoint ℂ)
    (hnc : ∀ x, ¬ ∀ᶠ x' in 𝓝 x, F x' = F x)
    (φ φ' : OpenPartialHomeomorph X ℂ)
    (hφ : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target)
    (hφ' : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ'.symm) φ'.target)
    (T : X → X) (hT : Continuous T) (hTi : Function.Injective T) (hFT : ∀ x, F (T x) = F x)
    (z : ℂ) (hz : z ∈ φ.target) (hTz : T (φ.symm z) ∈ φ'.source) :
    AnalyticAt ℂ (φ' ∘ T ∘ φ.symm) z := by
  set O : Set ℂ := φ.target ∩ φ.symm ⁻¹' (T ⁻¹' φ'.source) with hOdef
  have hO : IsOpen O := φ.continuousOn_symm.isOpen_inter_preimage φ.open_target
    (φ'.open_source.preimage hT)
  have hzO : z ∈ O := ⟨hz, hTz⟩
  have hhc : ContinuousOn (φ' ∘ T ∘ φ.symm) O :=
    φ'.continuousOn.comp (hT.comp_continuousOn (φ.continuousOn_symm.mono inter_subset_left))
      fun w hw ↦ hw.2
  have hinj : InjOn (φ' ∘ T ∘ φ.symm) O := by
    intro a ha a' ha' e
    exact φ.symm.injOn ha.1 ha'.1 (hTi (φ'.injOn ha.2 ha'.2 e))
  set p := φ' (T (φ.symm z))
  set y := F (φ.symm z)
  have hp : p ∈ φ'.target := φ'.map_source hTz
  have hpy : F (φ'.symm p) = y := by
    simp only [p, y, φ'.left_inv hTz, hFT]
  have hy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have ha₁ := b63g5_analyticAt_chart_comp φ.open_target hφ hz y hy
  have ha₂ := b63g5_analyticAt_chart_comp φ'.open_target hφ' hp y (by rw [Function.comp_apply, hpy]; exact hy)
  refine b63g5_analyticAt_of_comp (a₁ := chartAt ℂ y ∘ F ∘ φ.symm)
    (a₂ := chartAt ℂ y ∘ F ∘ φ'.symm) ?_ ⟨O, hO.mem_nhds hzO, hinj⟩ ha₁ ha₂ ?_ ?_
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hhc.continuousAt (hO.mem_nhds hw)
  · -- `F` is not constant near `φ'.symm p`
    intro hev
    apply hnc (φ'.symm p)
    have hcont : ContinuousAt (F ∘ φ'.symm) p :=
      hφ'.continuousOn.continuousAt (φ'.open_target.mem_nhds hp)
    have hsrc : ∀ᶠ w in 𝓝 p, (F ∘ φ'.symm) w ∈ (chartAt ℂ y).source :=
      hcont.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds
        (by rw [Function.comp_apply, hpy]; exact hy))
    have hconst : ∀ᶠ w in 𝓝 p, F (φ'.symm w) = y := by
      filter_upwards [hev, hsrc] with w hw hws
      have hps : (F ∘ φ'.symm) p ∈ (chartAt ℂ y).source := by
        rw [Function.comp_apply, hpy]; exact hy
      have := (chartAt ℂ y).injOn hws hps hw
      rw [Function.comp_apply, Function.comp_apply, hpy] at this
      exact this
    have hx' : φ'.symm p ∈ φ'.source := φ'.map_target hp
    have hmap : ∀ᶠ x' in 𝓝 (φ'.symm p), φ' x' ∈ {w | F (φ'.symm w) = y} := by
      have := (φ'.continuousAt hx').preimage_mem_nhds (by rw [φ'.right_inv hp]; exact hconst)
      exact this
    filter_upwards [hmap, φ'.open_source.mem_nhds hx'] with x' hx'1 hx'2
    rw [hpy]
    simpa [φ'.left_inv hx'2] using hx'1
  · filter_upwards [hO.mem_nhds hzO] with w hw
    simp only [Function.comp_apply, φ'.left_inv hw.2, hFT]

/-- The atlas of all charts in which `F` is holomorphic, when they cover `X`. -/
@[instance_reducible]
def b63g5_chartedSpace (F : X → OnePoint ℂ)
    (hcover : ∀ x, ∃ φ : OpenPartialHomeomorph X ℂ, x ∈ φ.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target) : ChartedSpace ℂ X where
  atlas := {φ | ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target}
  chartAt x := (hcover x).choose
  mem_chart_source x := (hcover x).choose_spec.1
  chart_mem_atlas x := (hcover x).choose_spec.2

/-- **A complex structure from charts in which `F` is holomorphic.** If the charts in which a
continuous, nowhere locally constant `F : X → ℙ¹` is holomorphic cover `X`, they form a complex
atlas; `F` is holomorphic for it, and so is every continuous injective `T` with `F ∘ T = F`. -/
theorem b63g5_exists_structure (F : X → OnePoint ℂ) (hF : Continuous F)
    (hnc : ∀ x, ¬ ∀ᶠ x' in 𝓝 x, F x' = F x)
    (hcover : ∀ x, ∃ φ : OpenPartialHomeomorph X ℂ, x ∈ φ.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target) :
    ∃ (_ : ChartedSpace ℂ X) (_ : IsManifold 𝓘(ℂ, ℂ) ω X),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F ∧
      ∀ T : X → X, Continuous T → Function.Injective T → (∀ x, F (T x) = F x) →
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω T := by
  let _ : ChartedSpace ℂ X := b63g5_chartedSpace F hcover
  have hgood : ∀ φ ∈ atlas ℂ X, ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target :=
    fun φ hφ ↦ hφ
  have hman : IsManifold 𝓘(ℂ, ℂ) ω X := by
    refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
      preimage_id_eq, id_eq, inter_univ, Function.id_comp, Function.comp_id]
    refine AnalyticOnNhd.contDiffOn_of_completeSpace fun z hz ↦ ?_
    have hz' : z ∈ e.target ∧ e.symm z ∈ e'.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hz
    exact b63g5_written_analyticAt F hnc e e' (hgood e he) (hgood e' he') id continuous_id
      Function.injective_id (fun _ ↦ rfl) z hz'.1 hz'.2
  refine ⟨inferInstance, hman, fun x ↦ ?_, fun T hT hTi hFT x ↦ ?_⟩
  · rw [contMDiffAt_iff]
    refine ⟨hF.continuousAt, ?_⟩
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, range_id, contDiffWithinAt_univ, Function.id_comp,
      Function.comp_id]
    have hx := mem_chart_source ℂ x
    have := b63g5_analyticAt_chart_comp (chartAt ℂ x).open_target
      (hgood _ (chart_mem_atlas ℂ x)) ((chartAt ℂ x).map_source hx) (F x)
      (by simp [(chartAt ℂ x).left_inv hx])
    exact this.self_of_nhds.contDiffAt
  · rw [contMDiffAt_iff]
    refine ⟨hT.continuousAt, ?_⟩
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, range_id, contDiffWithinAt_univ, Function.id_comp,
      Function.comp_id]
    have hx := mem_chart_source ℂ x
    have := b63g5_written_analyticAt F hnc (chartAt ℂ x) (chartAt ℂ (T x))
      (hgood _ (chart_mem_atlas ℂ x)) (hgood _ (chart_mem_atlas ℂ (T x))) T hT hTi hFT
      _ ((chartAt ℂ x).map_source hx)
      (by rw [(chartAt ℂ x).left_inv hx]; exact mem_chart_source ℂ (T x))
    exact this.contDiffAt

end Atlas

end HodgeLean.Foundations.Program
