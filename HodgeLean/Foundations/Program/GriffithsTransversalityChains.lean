import HodgeLean.Foundations.Program.GriffithsTransversalityResidues

/-! Retained-chart polygons on the fibres of the shared family: the retained fibre
coordinates as partial homeomorphisms, segment paths in them, and the period of a
holomorphic form along a polygon as a sum of segment integrals.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

section B66gRetainedChart

/-- Inverse of a retained fibre coordinate. -/
def b66g_inv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R) (w : ℂ) :
    rf8_fibre R.C t :=
  b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2

theorem b66g_inv_val (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    {w : ℂ} (hw : w ∈ b66k_domain R t a) :
    (b66g_inv R t a w).val = (R.atlas.A a).symm (t.val, w) :=
  b66k_inverse_slice R t a w hw

theorem b66g_inv_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    {w : ℂ} (hw : w ∈ b66k_domain R t a) :
    (b66g_inv R t a w).val ∈ (R.atlas.A a).source := by
  rw [b66g_inv_val R t a hw]
  exact (R.atlas.A a).map_target hw

theorem b66g_slice_inv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    {w : ℂ} (hw : w ∈ b66k_domain R t a) : b66g_slice R t a (b66g_inv R t a w) = w := by
  change (R.atlas.A a (b66g_inv R t a w).val).2 = w
  rw [b66g_inv_val R t a hw, (R.atlas.A a).right_inv hw]

theorem b66g_inv_slice_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    b66g_inv R t a (b66g_slice R t a y) = y := by
  change b66g_pt R t ((R.atlas.A a).symm (t.val, b66g_slice R t a y)).2 = y
  rw [b66g_inv_slice R t a y hy]
  exact b66g_fibre_mk R t y

theorem b66g_domain_open (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) : IsOpen (b66k_domain R t a) :=
  (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)

/-- A retained fibre coordinate as an open partial homeomorphism of the fibre.
Source: Forster, *Lectures on Riemann Surfaces*, §1, charts; `rf7_HurwitzAtlas.A`. -/
def b66g_rchart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R) :
    OpenPartialHomeomorph (rf8_fibre R.C t) ℂ where
  toFun := b66g_slice R t a
  invFun := b66g_inv R t a
  source := {y | y.val ∈ (R.atlas.A a).source}
  target := b66k_domain R t a
  map_source' := fun y hy => b66g_slice_domain R t a y hy
  map_target' := fun _ hw => b66g_inv_mem R t a hw
  left_inv' := fun y hy => b66g_inv_slice_eq R t a y hy
  right_inv' := fun _ hw => b66g_slice_inv R t a hw
  open_source := b66g_open_source R t a
  open_target := b66g_domain_open R t a
  continuousOn_toFun := fun y hy =>
    (b66g_slice_contMDiffAt R t a y hy).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw => (b66g_pt_continuous R t a w hw).continuousWithinAt

theorem b66g_inv_contMDiffAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) {w : ℂ} (hw : w ∈ b66k_domain R t a) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_inv R t a) w := by
  rw [contMDiffAt_iff_target]
  refine ⟨b66g_pt_continuous R t a w hw, ?_⟩
  have h := b66g_coord_analytic R t (extChartAt 𝓘(ℂ, ℂ) (b66g_inv R t a w)) a w hw
    (contMDiffAt_extChartAt)
  exact contMDiffAt_iff_contDiffAt.mpr h.contDiffAt

/-- The derivative of a retained coordinate along a `C¹` path is the coordinate derivative
applied to the velocity. -/
theorem b66g_slice_hasDerivAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (γ : ℝ → rf8_fibre R.C t) (s : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s) (ha : (γ s).val ∈ (R.atlas.A a).source) :
    HasDerivAt (b66g_slice R t a ∘ γ)
      (b66g_sliceD R t a (γ s) (b3_velocity ℂ (rf8_fibre R.C t) γ s)) s := by
  set x := γ s
  set e := extChartAt 𝓘(ℂ, ℂ) x
  set g := b66g_slice R t a ∘ e.symm
  obtain ⟨hg, -, -⟩ := b66g_slice_chart R t a x x (mem_extChartAt_source x) ha
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s := hγ.mdifferentiableAt one_ne_zero
  have hv := b3A_velocity_eq_fderiv γ s hm
  obtain ⟨hcd, -⟩ := b3A_chart_comp γ s hγ x (mem_chart_source ℂ x)
  have hc : HasDerivAt (chartAt ℂ x ∘ γ) (b3_velocity ℂ (rf8_fibre R.C t) γ s) s := by
    have := (hcd.differentiableAt one_ne_zero).hasFDerivAt.hasDerivAt
    rw [hv]
    exact this
  have hce : e x = (chartAt ℂ x ∘ γ) s := by simp [e, x]
  have hgd : HasFDerivAt g (fderiv ℂ g ((chartAt ℂ x ∘ γ) s)) ((chartAt ℂ x ∘ γ) s) := by
    rw [← hce]
    exact hg.differentiableAt.hasFDerivAt
  have hcomp := (hgd.restrictScalars ℝ).comp_hasDerivAt s hc
  have hsl : b66g_sliceD R t a x = fderiv ℂ g (e x) := by
    have hd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) x :=
      (b66g_slice_contMDiffAt R t a x ha).mdifferentiableAt (by simp)
    rw [b66g_sliceD, hd.mfderiv]
    simp [writtenInExtChartAt, g, e, tangentSpaceCastModel]
    rfl
  have hev : b66g_slice R t a ∘ γ =ᶠ[𝓝 s] g ∘ (chartAt ℂ x ∘ γ) := by
    filter_upwards [hm.continuousAt.preimage_mem_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))] with u hu
    simp only [Function.comp_apply, g, e, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [(chartAt ℂ x).left_inv hu]
  rw [hsl, hce]
  exact hcomp.congr_of_eventuallyEq hev

end B66gRetainedChart

section B66gFloor

variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]

omit [IsManifold 𝓘(ℂ, ℂ) ω C] in
/-- Near the unit interval `[k, k + 1]` the floor-glued path is a translate of one piece. -/
theorem b66g_floor_eventually (γ : ℤ → ℝ → C) (z : ℤ → C)
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) (k : ℤ) {v : ℝ}
    (hv : v ∈ Icc (k : ℝ) (k + 1)) :
    (fun v => γ ⌊v⌋ (Int.fract v)) =ᶠ[𝓝 v] fun v => γ k (v - k) := by
  have hR : ∀ᶠ w in 𝓝 ((k : ℝ) + 1), γ k (w - k) = z (k + 1) := by
    have ht : Tendsto (fun w : ℝ => w - k) (𝓝 ((k : ℝ) + 1)) (𝓝 1) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    exact ht.eventually (hγ k).2.2
  have hR' : ∀ᶠ w in 𝓝 ((k : ℝ) + 1), γ (k + 1) (w - ((k : ℝ) + 1)) = z (k + 1) := by
    have ht : Tendsto (fun w : ℝ => w - ((k : ℝ) + 1)) (𝓝 ((k : ℝ) + 1)) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    exact ht.eventually (hγ (k + 1)).2.1
  have hL : ∀ᶠ w in 𝓝 (k : ℝ), γ k (w - k) = z k := by
    have ht : Tendsto (fun w : ℝ => w - k) (𝓝 (k : ℝ)) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    exact ht.eventually (hγ k).2.1
  have hL' : ∀ᶠ w in 𝓝 (k : ℝ), γ (k - 1) (w - ((k : ℝ) - 1)) = z k := by
    have ht : Tendsto (fun w : ℝ => w - ((k : ℝ) - 1)) (𝓝 (k : ℝ)) (𝓝 1) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    have := ht.eventually (hγ (k - 1)).2.2
    simpa only [sub_add_cancel] using this
  rcases hv.1.lt_or_eq with h0 | h0
  · rcases hv.2.lt_or_eq with h1 | h1
    · filter_upwards [Ioo_mem_nhds h0 h1] with w hw
      have hfl : ⌊w⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨hw.1.le, hw.2⟩
      show γ ⌊w⌋ (Int.fract w) = γ k (w - k)
      rw [Int.fract, hfl]
    · subst h1
      filter_upwards [hR, hR', Ioo_mem_nhds (show (k : ℝ) < k + 1 by linarith)
        (show (k : ℝ) + 1 < k + 2 by linarith)] with w hA hB hw
      show γ ⌊w⌋ (Int.fract w) = γ k (w - k)
      rcases lt_or_ge w ((k : ℝ) + 1) with hlt | hle
      · have hfl : ⌊w⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨hw.1.le, hlt⟩
        rw [Int.fract, hfl]
      · have hfl : ⌊w⌋ = k + 1 := by
          rw [Int.floor_eq_iff]; push_cast; exact ⟨hle, by linarith [hw.2]⟩
        rw [Int.fract, hfl]
        push_cast
        rw [hB, hA]
  · subst h0
    filter_upwards [hL, hL', Ioo_mem_nhds (show (k : ℝ) - 1 < k by linarith)
      (show (k : ℝ) < k + 1 by linarith)] with w hA hB hw
    show γ ⌊w⌋ (Int.fract w) = γ k (w - k)
    rcases lt_or_ge w (k : ℝ) with hlt | hle
    · have hfl : ⌊w⌋ = k - 1 := by
        rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith [hw.1], by linarith⟩
      rw [Int.fract, hfl]
      push_cast
      rw [hB, hA]
    · have hfl : ⌊w⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨hle, hw.2⟩
      rw [Int.fract, hfl]

/-- The integral of a holomorphic form along `N` good paths glued at the points `k / N` is the
sum of the integrals along the pieces. -/
theorem b66g_floor_pathIntegral {θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ} (hθ : θ ∈ b3_HolForm ℂ C)
    (N : ℕ) (γ : ℤ → ℝ → C) (z : ℤ → C)
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) :
    b3_pathIntegral ℂ C (fun σ => γ ⌊(N : ℝ) * σ⌋ (Int.fract ((N : ℝ) * σ))) θ =
      ∑ k ∈ Finset.range N, b3_pathIntegral ℂ C (γ k) θ := by
  set G : ℝ → C := fun v => γ ⌊v⌋ (Int.fract v)
  have hG : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 G := b3Rest_floorPath_contMDiff γ z hγ
  have h1 := b3A_integral_reparam hθ G hG (fun σ => (N : ℝ) * σ)
    (contDiff_const.mul contDiff_id) 0 1
  simp only [mul_zero, mul_one] at h1
  change ∫ σ in (0 : ℝ)..1, b3A_integrand θ (G ∘ fun σ => (N : ℝ) * σ) σ = _
  rw [h1]
  have hint : ∀ k < N, IntervalIntegrable (b3A_integrand θ G) MeasureTheory.volume
      ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := fun k _ =>
    (b3A_continuous_integrand G hG ⟨θ, hθ⟩).intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcongr : ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), b3A_integrand θ G v =
      ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ),
        b3A_integrand θ (γ (k : ℤ) ∘ fun v => v - ((k : ℤ) : ℝ)) v := by
    refine intervalIntegral.integral_congr fun v hv => b3A_integrand_congr θ ?_
    rw [uIcc_of_le (by push_cast; linarith)] at hv
    have hv' : v ∈ Icc ((k : ℤ) : ℝ) ((k : ℤ) + 1) := by push_cast at hv ⊢; exact hv
    exact b66g_floor_eventually γ z hγ k hv'
  rw [hcongr, b3A_integral_reparam hθ (γ k) (hγ k).1 (fun v => v - ((k : ℤ) : ℝ))
    (contDiff_id.sub contDiff_const)]
  push_cast
  simp only [sub_self, add_sub_cancel_left]
  rfl

end B66gFloor

section B66gSegments

/-- Point of a retained segment, reparametrized by the smooth step. -/
def b66g_segPt (c e : ℂ) (τ : ℝ) : ℂ := c + (b3A_step τ : ℂ) * (e - c)

theorem b66g_step_mem (τ : ℝ) : b3A_step τ ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The segment condition in a retained chart of a fibre. -/
def b66g_SegIn (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (c e : ℂ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) 1, c + (r : ℂ) * (e - c) ∈ b66k_domain R t a

/-- The segment path in a retained chart of a fibre. -/
def b66g_seg (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (c e : ℂ) (τ : ℝ) : rf8_fibre R.C t :=
  b66g_inv R t a (b66g_segPt c e τ)

theorem b66g_segPt_mem {R : rf8_SharedFamily} {t : b6t_polydisc mr_base} {a : b66k_Index R}
    {c e : ℂ} (h : b66g_SegIn R t a c e) (τ : ℝ) : b66g_segPt c e τ ∈ b66k_domain R t a :=
  h _ (b66g_step_mem τ)

theorem b66g_segPt_contDiff (c e : ℂ) : ContDiff ℝ 1 (b66g_segPt c e) :=
  contDiff_const.add ((Complex.ofRealCLM.contDiff.comp b3A_step_contDiff).mul contDiff_const)

theorem b66g_segPt_hasDerivAt (c e : ℂ) (τ : ℝ) :
    HasDerivAt (b66g_segPt c e) (((deriv b3A_step τ : ℝ) : ℂ) * (e - c)) τ := by
  have hs : HasDerivAt b3A_step (deriv b3A_step τ) τ :=
    ((b3A_step_contDiff.differentiable one_ne_zero) τ).hasDerivAt
  have := (hs.ofReal_comp.mul_const (e - c)).const_add c
  exact this

theorem b66g_seg_good (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    {c e : ℂ} (h : b66g_SegIn R t a c e) :
    b3A_IsGoodPath (E := ℂ) (b66g_seg R t a c e) (b66g_inv R t a c) (b66g_inv R t a e) := by
  refine ⟨fun τ => ?_, ?_, ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_inv R t a) (b66g_segPt c e τ) :=
      b66g_inv_contMDiffAt R t a (b66g_segPt_mem h τ)
    have h2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (b66g_inv R t a) (b66g_segPt c e τ) :=
      (b3A_contMDiffWithinAt_real h1).of_le le_top
    exact h2.comp τ ((b66g_segPt_contDiff c e).contMDiff τ)
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with τ hτ
    have : b3A_step τ = 0 := Real.smoothTransition.zero_of_nonpos (by
      have : τ < 1 / 3 := hτ
      linarith)
    simp [b66g_seg, b66g_segPt, this]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with τ hτ
    have : b3A_step τ = 1 := Real.smoothTransition.one_of_one_le (by
      have : 2 / 3 < τ := hτ
      linarith)
    simp [b66g_seg, b66g_segPt, this]

/-- The integral of a form along a retained segment, from its chart coefficient. -/
theorem b66g_seg_integral (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) {c e : ℂ} (h : b66g_SegIn R t a c e)
    (η : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) (f : ℂ → ℂ)
    (hη : ∀ y : rf8_fibre R.C t, y.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
      η ⟨y, v⟩ = f (b66g_slice R t a y) * b66g_sliceD R t a y v)
    (hf : ContinuousOn f (b66k_domain R t a)) :
    b3_pathIntegral ℂ (rf8_fibre R.C t) (b66g_seg R t a c e) η =
      ∫ r in (0 : ℝ)..1, f (c + (r : ℂ) * (e - c)) * (e - c) := by
  have hgood := b66g_seg_good R t a h
  have hpt : ∀ τ : ℝ, η ⟨b66g_seg R t a c e τ,
      b3_velocity ℂ (rf8_fibre R.C t) (b66g_seg R t a c e) τ⟩ =
      deriv b3A_step τ • (fun r : ℝ => f (c + (r : ℂ) * (e - c)) * (e - c)) (b3A_step τ) := by
    intro τ
    have hmem := b66g_inv_mem R t a (b66g_segPt_mem h τ)
    have hd := b66g_slice_hasDerivAt R t a (b66g_seg R t a c e) τ (hgood.1 τ) hmem
    have hfun : b66g_slice R t a ∘ b66g_seg R t a c e = b66g_segPt c e := by
      funext σ
      exact b66g_slice_inv R t a (b66g_segPt_mem h σ)
    rw [hfun] at hd
    have hv := hd.unique (b66g_segPt_hasDerivAt c e τ)
    refine (hη (b66g_seg R t a c e τ) hmem
      (b3_velocity ℂ (rf8_fibre R.C t) (b66g_seg R t a c e) τ)).trans ?_
    rw [hv]
    change f (b66g_slice R t a (b66g_inv R t a (b66g_segPt c e τ))) * _ = _
    rw [b66g_slice_inv R t a (b66g_segPt_mem h τ), Complex.real_smul]
    simp only [b66g_segPt]
    ring
  change ∫ τ in (0 : ℝ)..1, η ⟨b66g_seg R t a c e τ,
      b3_velocity ℂ (rf8_fibre R.C t) (b66g_seg R t a c e) τ⟩ = _
  rw [intervalIntegral.integral_congr (fun τ _ => hpt τ)]
  have h0 : b3A_step 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : b3A_step 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := 1)
    (f := b3A_step) (f' := deriv b3A_step)
    (g := fun r : ℝ => f (c + (r : ℂ) * (e - c)) * (e - c))
    (fun τ _ => ((b3A_step_contDiff.differentiable one_ne_zero) τ).hasDerivAt)
    (b3A_step_contDiff.continuous_deriv le_rfl).continuousOn ?_
  · rw [h0, h1] at hsub
    exact hsub
  · have hc : ContinuousOn (fun r : ℝ => c + (r : ℂ) * (e - c)) (Icc 0 1) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    have hfc : ContinuousOn (fun r : ℝ => f (c + (r : ℂ) * (e - c))) (Icc 0 1) :=
      hf.comp hc (fun r hr => h r hr)
    refine (hfc.mul continuousOn_const).mono ?_
    rintro _ ⟨τ, -, rfl⟩
    exact b66g_step_mem τ

end B66gSegments

section B66gLoopClass

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters

/-- Integral class of a continuous `1`-periodic path.
Source: Hatcher, *Algebraic Topology*, §2.A; `b6m_loopClass`. -/
def b66g_cls {X : Type} [TopologicalSpace X] (p : ℝ → X) (hp : Continuous p)
    (hper : Function.Periodic p 1) : b6m_H1 X :=
  ((SingularChainComplex ℤ (TopCat.of X)).sc 1).moduleCatHomologyClass
    (loopCycle ℤ ⟨hper.lift, by
      rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
      exact hp⟩)

theorem b66g_loopClass_eq_cls {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (γ : b3_SmoothLoop ℂ X) :
    b6m_loopClass X γ = b66g_cls γ.1 γ.2.2.continuous γ.2.1 := rfl

theorem b66g_cls_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (p : ℝ → X) (hp : Continuous p) (hper : Function.Periodic p 1) :
    b6m_H1Equiv e (b66g_cls p hp hper) =
      b66g_cls (e ∘ p) (e.continuous.comp hp) (fun σ => by simp [hper σ]) := by
  change homologyMap ℤ 1 (TopCat.ofHom ⟨e, e.continuous⟩) _ = _
  rw [b66g_cls, b6m_homologyMap_loopCycle]
  congr 2

theorem b66g_cls_homotopy {X : Type} [TopologicalSpace X] (H : unitInterval × ℝ → X)
    (hH : Continuous H) (hper : ∀ s σ, H (s, σ + 1) = H (s, σ)) :
    b66g_cls (fun σ => H (0, σ)) (hH.comp (continuous_const.prodMk continuous_id))
        (fun σ => hper 0 σ) =
      b66g_cls (fun σ => H (1, σ)) (hH.comp (continuous_const.prodMk continuous_id))
        (fun σ => hper 1 σ) := by
  have hp : ∀ s : unitInterval, Function.Periodic (fun σ => H (s, σ)) 1 := fun s σ => hper s σ
  let Hc : unitInterval × UnitAddCircle → X := fun z => (hp z.1).lift z.2
  have hHc : Continuous Hc := by
    rw [← (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    exact hH
  refine b6m_integral_loopClass_homotopy
    { toFun := Hc
      continuous_toFun := hHc
      map_zero_left := fun z => ?_
      map_one_left := fun z => ?_ }
  · obtain ⟨σ, rfl⟩ := QuotientAddGroup.mk_surjective z
    rfl
  · obtain ⟨σ, rfl⟩ := QuotientAddGroup.mk_surjective z
    rfl

end B66gLoopClass

section B66gPoly

/-- A polygon loop in retained charts. The `k`-th side lies in the chart `a k`, starts at the
point with coordinate `c k` there, and ends at the start of side `k + 1`. Indices are
`N`-periodic. The sides move with the parameter at fixed start coordinates.
Source: Forster, *Lectures on Riemann Surfaces*, §20, paths through coordinate discs;
`b3Rest_Cover`. -/
structure b66g_Poly (R : rf8_SharedFamily) where
  N : ℕ
  pos : 0 < N
  a : ℤ → b66k_Index R
  c : ℤ → ℂ
  a_add : ∀ k, a (k + N) = a k
  c_add : ∀ k, c (k + N) = c k

namespace b66g_Poly

variable {R : rf8_SharedFamily} (D : b66g_Poly R)

/-- End coordinate of the `k`-th side over the parameter `u`, in the chart of that side. -/
def E (u : Fin 10 → ℂ) (k : ℤ) : ℂ :=
  b66k_transition R (D.a (k + 1)) (D.a k) (u, D.c (k + 1))

/-- The polygon is defined over the parameter `u`. -/
def Valid (u : b6t_polydisc mr_base) : Prop := ∀ k : ℤ,
  b66g_SegIn R u (D.a k) (D.c k) (D.E u.val k) ∧ D.c (k + 1) ∈ b66k_domain R u (D.a (k + 1)) ∧
    (b66g_inv R u (D.a (k + 1)) (D.c (k + 1))).val ∈ (R.atlas.A (D.a k)).source

/-- The `k`-th vertex over `u`. -/
def V (u : b6t_polydisc mr_base) (k : ℤ) : rf8_fibre R.C u := b66g_inv R u (D.a k) (D.c k)

/-- The `k`-th side over `u`. -/
def side (u : b6t_polydisc mr_base) (k : ℤ) : ℝ → rf8_fibre R.C u :=
  b66g_seg R u (D.a k) (D.c k) (D.E u.val k)

theorem E_add (u : Fin 10 → ℂ) (k : ℤ) : D.E u (k + D.N) = D.E u k := by
  simp only [E, add_right_comm k (D.N : ℤ) 1, D.a_add, D.c_add]

theorem side_add (u : b6t_polydisc mr_base) (k : ℤ) : D.side u (k + D.N) = D.side u k := by
  simp only [side, D.a_add, D.c_add, D.E_add]

theorem E_eq_slice {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ) :
    D.E u.val k = b66g_slice R u (D.a k) (D.V u (k + 1)) := by
  change b66k_transition R (D.a (k + 1)) (D.a k) (u.val, D.c (k + 1)) =
    (R.atlas.A (D.a k) (D.V u (k + 1)).val).2
  rw [show (D.V u (k + 1)).val = (R.atlas.A (D.a (k + 1))).symm (u.val, D.c (k + 1)) from
    b66g_inv_val R u (D.a (k + 1)) (hv k).2.1]
  rfl

theorem inv_E {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ) :
    b66g_inv R u (D.a k) (D.E u.val k) = D.V u (k + 1) := by
  rw [D.E_eq_slice hv k]
  exact b66g_inv_slice_eq R u (D.a k) _ (hv k).2.2

theorem side_good {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ) :
    b3A_IsGoodPath (E := ℂ) (D.side u k) (D.V u k) (D.V u (k + 1)) := by
  have h := b66g_seg_good R u (D.a k) (hv k).1
  rw [D.inv_E hv k] at h
  exact h

/-- The polygon loop over `u`, glued from its sides at the points `k / N`. -/
def loop (u : b6t_polydisc mr_base) (σ : ℝ) : rf8_fibre R.C u :=
  D.side u ⌊(D.N : ℝ) * σ⌋ (Int.fract ((D.N : ℝ) * σ))

theorem loop_periodic (u : b6t_polydisc mr_base) : Function.Periodic (D.loop u) 1 := by
  intro σ
  have h : (D.N : ℝ) * (σ + 1) = (D.N : ℝ) * σ + ((D.N : ℤ) : ℝ) := by push_cast; ring
  simp only [loop, h, Int.floor_add_intCast, Int.fract_add_intCast, D.side_add]

theorem loop_contMDiff {u : b6t_polydisc mr_base} (hv : D.Valid u) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (D.loop u) :=
  (b3Rest_floorPath_contMDiff (D.side u) (D.V u) (D.side_good hv)).comp
    (contDiff_const.mul contDiff_id).contMDiff

/-- The polygon over `u` as a `C¹` loop of the fibre. -/
def smoothLoop {u : b6t_polydisc mr_base} (hv : D.Valid u) : b3_SmoothLoop ℂ (rf8_fibre R.C u) :=
  ⟨D.loop u, D.loop_periodic u, D.loop_contMDiff hv⟩

/-- The period of a holomorphic form along the polygon is the sum of the segment integrals
of its chart coefficients. -/
theorem period_eq {u : b6t_polydisc mr_base} (hv : D.Valid u)
    (θ : b3_HolForm ℂ (rf8_fibre R.C u)) (f : ℤ → ℂ → ℂ)
    (hf : ∀ k, ∀ y : rf8_fibre R.C u, y.val ∈ (R.atlas.A (D.a k)).source → ∀ v : ℂ,
      θ.1 ⟨y, v⟩ = f k (b66g_slice R u (D.a k) y) * b66g_sliceD R u (D.a k) y v)
    (hfc : ∀ k, ContinuousOn (f k) (b66k_domain R u (D.a k))) :
    b3_period ℂ (rf8_fibre R.C u) (D.smoothLoop hv) θ =
      ∑ k ∈ Finset.range D.N, ∫ r in (0 : ℝ)..1,
        f k (D.c k + (r : ℂ) * (D.E u.val k - D.c k)) * (D.E u.val k - D.c k) := by
  change b3_pathIntegral ℂ (rf8_fibre R.C u)
    (fun σ => D.side u ⌊(D.N : ℝ) * σ⌋ (Int.fract ((D.N : ℝ) * σ))) θ.1 = _
  rw [b66g_floor_pathIntegral θ.2 D.N (D.side u) (D.V u) (D.side_good hv)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact b66g_seg_integral R u (D.a k) (hv k).1 θ.1 (f k) (hf k) (hfc k)

/-- The `k`-th side over the parameter `u`, read in `C`. -/
def sideC (u : Fin 10 → ℂ) (k : ℤ) (τ : ℝ) : R.C :=
  ((R.atlas.A (D.a k)).symm (u, b66g_segPt (D.c k) (D.E u k) τ)).2

/-- The polygon over the parameter `u`, read in `C`. -/
def loopC (u : Fin 10 → ℂ) (σ : ℝ) : R.C :=
  D.sideC u ⌊(D.N : ℝ) * σ⌋ (Int.fract ((D.N : ℝ) * σ))

theorem loop_eq (u : b6t_polydisc mr_base) (σ : ℝ) :
    D.loop u σ = b66g_pt R u (D.loopC u.val σ) := rfl

theorem sideC_add (u : Fin 10 → ℂ) (k : ℤ) : D.sideC u (k + D.N) = D.sideC u k := by
  funext τ
  simp only [sideC, D.a_add, D.c_add, D.E_add]

theorem loopC_periodic (u : Fin 10 → ℂ) : Function.Periodic (D.loopC u) 1 := by
  intro σ
  have h : (D.N : ℝ) * (σ + 1) = (D.N : ℝ) * σ + ((D.N : ℤ) : ℝ) := by push_cast; ring
  change D.sideC u ⌊(D.N : ℝ) * (σ + 1)⌋ (Int.fract ((D.N : ℝ) * (σ + 1))) =
    D.sideC u ⌊(D.N : ℝ) * σ⌋ (Int.fract ((D.N : ℝ) * σ))
  rw [h, Int.floor_add_intCast, Int.fract_add_intCast, D.sideC_add]

theorem E_continuousAt {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ) :
    ContinuousAt (fun w : Fin 10 → ℂ => D.E w k) u.val := by
  have h1 : (u.val, D.c (k + 1)) ∈ (R.atlas.A (D.a (k + 1))).target := (hv k).2.1
  have h2 : (R.atlas.A (D.a (k + 1))).symm (u.val, D.c (k + 1)) ∈ (R.atlas.A (D.a k)).source := by
    have := (hv k).2.2
    rwa [b66g_inv_val R u (D.a (k + 1)) (hv k).2.1] at this
  have hs : ContinuousAt (fun w : Fin 10 → ℂ => (R.atlas.A (D.a (k + 1))).symm (w, D.c (k + 1)))
      u.val :=
    ((R.atlas.A (D.a (k + 1))).continuousAt_symm h1).comp
      (f := fun w : Fin 10 → ℂ => (w, D.c (k + 1)))
      (continuous_id.prodMk continuous_const).continuousAt
  exact continuous_snd.continuousAt.comp (((R.atlas.A (D.a k)).continuousAt h2).comp
    (f := fun w : Fin 10 → ℂ => (R.atlas.A (D.a (k + 1))).symm (w, D.c (k + 1))) hs)

theorem sideC_continuousAt {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ)
    {Y : Type} [TopologicalSpace Y] (w : Y → Fin 10 → ℂ) (τ : Y → ℝ) (y₀ : Y)
    (hw : ContinuousAt w y₀) (hτ : ContinuousAt τ y₀) (hw₀ : w y₀ = u.val) :
    ContinuousAt (fun y => D.sideC (w y) k (τ y)) y₀ := by
  have hmem : (w y₀, b66g_segPt (D.c k) (D.E (w y₀) k) (τ y₀)) ∈
      (R.atlas.A (D.a k)).target := by
    rw [hw₀]
    exact (hv k).1 _ (b66g_step_mem (τ y₀))
  have hE : ContinuousAt (fun y => D.E (w y) k) y₀ := by
    have := D.E_continuousAt hv k
    rw [← hw₀] at this
    exact this.comp hw
  have hstep : Continuous b3A_step := b3A_step_contDiff.continuous
  have hpt : ContinuousAt (fun y => b66g_segPt (D.c k) (D.E (w y) k) (τ y)) y₀ := by
    unfold b66g_segPt
    exact continuousAt_const.add
      ((Complex.continuous_ofReal.continuousAt.comp (hstep.continuousAt.comp hτ)).mul
        (hE.sub continuousAt_const))
  exact continuous_snd.continuousAt.comp
    (((R.atlas.A (D.a k)).continuousAt_symm hmem).comp
      (f := fun y => (w y, b66g_segPt (D.c k) (D.E (w y) k) (τ y))) (hw.prodMk hpt))

theorem sideC_match {u : b6t_polydisc mr_base} (hv : D.Valid u) (k : ℤ) :
    D.sideC u.val k 1 = D.sideC u.val (k + 1) 0 := by
  have h0 : b3A_step 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : b3A_step 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have h := congrArg (fun y : rf8_fibre R.C u => y.val.2) (D.inv_E hv k)
  simp only [sideC, b66g_segPt, h0, h1, Complex.ofReal_zero, Complex.ofReal_one, one_mul,
    zero_mul, add_zero, add_sub_cancel]
  exact h

/-- The segment of parameters from `t` to `u`. -/
def lineP (t u : Fin 10 → ℂ) (s : ℝ) : Fin 10 → ℂ := t + (s : ℂ) • (u - t)

theorem lineP_continuous (t u : Fin 10 → ℂ) : Continuous (lineP t u) :=
  continuous_const.add ((Complex.continuous_ofReal.smul continuous_const))

/-- Over a segment of parameters on which the polygon is defined, the polygon over the end is
homologous to the transport of the polygon over the start. -/
theorem loopClass_transport {t u : b6t_polydisc mr_base}
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, ∃ h : lineP t.val u.val s ∈ b6t_polydisc mr_base,
      D.Valid ⟨_, h⟩) (ht : D.Valid t) (hu : D.Valid u) :
    b6m_loopClass (rf8_fibre R.C u) (D.smoothLoop hu) =
      b6m_H1Equiv (b6m_transport mr_base R.C t u)
        (b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop ht)) := by
  rw [b66g_loopClass_eq_cls, b66g_loopClass_eq_cls, b66g_cls_map]
  choose hP hV using hpath
  let G : ℤ → unitInterval → ℝ → R.C := fun k s τ => D.sideC (lineP t.val u.val s) k τ
  have hG : ∀ k, ContinuousOn (fun p : unitInterval × ℝ => G k p.1 p.2) (univ ×ˢ Icc 0 1) := by
    intro k
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun p => ?_)
    exact D.sideC_continuousAt (hV p.1 p.1.2) k (fun q : unitInterval × ℝ =>
      lineP t.val u.val q.1) (fun q => q.2) p
      ((lineP_continuous _ _).comp (continuous_subtype_val.comp continuous_fst)).continuousAt
      continuous_snd.continuousAt rfl
  have hm : ∀ k (s : unitInterval), G k s 1 = G (k + 1) s 0 := fun k s =>
    D.sideC_match (hV s s.2) k
  have hfl := b3Rest_continuous_floor G hG hm
  let H : unitInterval × ℝ → rf8_fibre R.C u := fun p =>
    b66g_pt R u (D.loopC (lineP t.val u.val p.1) p.2)
  have hH : Continuous H := by
    have hc : Continuous (fun p : unitInterval × ℝ => D.loopC (lineP t.val u.val p.1) p.2) :=
      hfl.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))
    exact (b6m_coordinate mr_base R.C u).symm.continuous.comp hc
  have hper : ∀ s σ, H (s, σ + 1) = H (s, σ) := fun s σ => by
    simp only [H, D.loopC_periodic _ σ]
  have hcls := b66g_cls_homotopy H hH hper
  have e0 : (fun σ => H (0, σ)) = (b6m_transport mr_base R.C t u) ∘ D.loop t := by
    funext σ
    simp only [H, lineP, Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul, add_zero]
    rfl
  have e1 : (fun σ => H (1, σ)) = D.loop u := by
    funext σ
    simp only [H, lineP, Set.Icc.coe_one, Complex.ofReal_one, one_smul, add_sub_cancel]
    rfl
  have key : ∀ (p q : ℝ → rf8_fibre R.C u) (hpq : p = q) (hp hq hp' hq'),
      b66g_cls p hp hp' = b66g_cls q hq hq' := by
    intro p q hpq _ _ _ _
    subst hpq
    rfl
  exact (key _ _ e1.symm _ _ _ _).trans (hcls.symm.trans (key _ _ e0 _ _ _ _))

end b66g_Poly

end B66gPoly

section B66gRetainedAtlas

/-- A fibre with the retained fibre coordinates as its atlas. It is only used to cut loops
into arcs inside retained charts.
Source: Forster, §1, equivalent atlases. -/
def b66g_RF (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) : Type := rf8_fibre R.C t

instance b66g_RF_top (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    TopologicalSpace (b66g_RF R t) :=
  inferInstanceAs (TopologicalSpace (rf8_fibre R.C t))

instance b66g_RF_charted (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ChartedSpace ℂ (b66g_RF R t) where
  atlas := range (b66g_rchart R t)
  chartAt y := b66g_rchart R t (show rf8_fibre R.C t from y).val
  mem_chart_source _ := (R.atlas.hA _).1
  chart_mem_atlas _ := mem_range_self _

theorem b66g_rchart_trans (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) {w : ℂ} (hw : w ∈ ((b66g_rchart R t a).symm ≫ₕ b66g_rchart R t b).source) :
    AnalyticAt ℂ ((b66g_rchart R t a).symm ≫ₕ b66g_rchart R t b) w ∧
      ((b66g_rchart R t a).symm ≫ₕ b66g_rchart R t b) w =
        b66k_transition R a b (t.val, w) := by
  have hwa : w ∈ b66k_domain R t a := hw.1
  have hwb : (b66g_inv R t a w).val ∈ (R.atlas.A b).source := hw.2
  have heq : ∀ z ∈ b66k_domain R t a,
      ((b66g_rchart R t a).symm ≫ₕ b66g_rchart R t b) z = b66k_transition R a b (t.val, z) :=
    fun z hz => by
      change (R.atlas.A b (b66g_inv R t a z).val).2 = _
      rw [b66g_inv_val R t a hz]
      rfl
  refine ⟨?_, heq w hwa⟩
  have hz : w ∈ b66k_refinementDomain R t 1 a b := by
    refine ⟨hwa, ?_⟩
    rw [one_smul]
    exact hwb
  refine (b66g_transition_mem R t a b w hz).2.2.1.congr ?_
  filter_upwards [(b66g_domain_open R t a).mem_nhds hwa] with z hz'
  exact (heq z hz').symm

instance b66g_RF_manifold (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    IsManifold 𝓘(ℂ, ℂ) ω (b66g_RF R t) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  intro w hw
  exact (b66g_rchart_trans R t a b hw).1.contDiffAt.contDiffWithinAt

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters in
/-- Every continuous loop of a fibre is homologous to a retained polygon over that fibre. -/
theorem b66g_exists_poly (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (p : C(UnitAddCircle, rf8_fibre R.C t)) :
    ∃ (D : b66g_Poly R) (hv : D.Valid t),
      b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop hv) =
        ((SingularChainComplex ℤ (TopCat.of (rf8_fibre R.C t))).sc 1).moduleCatHomologyClass
          (loopCycle ℤ p) := by
  let P : ℝ → b66g_RF R t := fun σ => p σ
  have hPc : Continuous P := p.continuous.comp (AddCircle.continuous_mk' 1)
  have hper : Function.Periodic P 1 := fun σ => by
    change p ((σ + 1 : ℝ) : UnitAddCircle) = p σ
    rw [AddCircle.coe_add_period]
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ := b3Rest_exists_chartCover (E := ℂ) P hPc hper
  let K : b3Rest_Cover ℂ P := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  let a : ℤ → b66k_Index R := fun k => (show rf8_fibre R.C t from x k).val
  have hch : ∀ k, chartAt ℂ (K.x k) = b66g_rchart R t (a k) := fun k => rfl
  let D : b66g_Poly R := ⟨N, hN, a, K.a, fun k => by simp only [a]; rw [hx k],
    fun k => K.a_add hper k⟩
  have hE : ∀ k, D.E t.val k = K.b k := by
    intro k
    have h1 := K.mem_one k
    have h0 := K.mem_zero (k + 1)
    have hy : P ((k + 1 : ℤ) / (N : ℝ)) = P ((k + 1) / N) := by push_cast; rfl
    change b66k_transition R (a (k + 1)) (a k) (t.val, K.a (k + 1)) = K.b k
    have hsrc : (show rf8_fibre R.C t from P ((k + 1 : ℤ) / (N : ℝ))).val ∈
        (R.atlas.A (a (k + 1))).source := h0.1
    change b66k_transition R (a (k + 1)) (a k)
        (t.val, b66g_slice R t (a (k + 1)) (P ((k + 1 : ℤ) / (N : ℝ)))) =
      b66g_slice R t (a k) (P ((k + 1) / N))
    have hdom := b66g_slice_domain R t (a (k + 1)) _ hsrc
    change (R.atlas.A (a k) ((R.atlas.A (a (k + 1))).symm (t.val,
      b66g_slice R t (a (k + 1)) (P ((k + 1 : ℤ) / (N : ℝ)))))).2 = _
    rw [← b66g_inv_val R t (a (k + 1)) hdom, b66g_inv_slice_eq R t (a (k + 1)) _ hsrc, hy]
    rfl
  have hv : D.Valid t := by
    intro k
    have h1 := K.mem_one k
    have h0 := K.mem_zero k
    have h0' := K.mem_zero (k + 1)
    refine ⟨fun ρ hρ => ?_, ?_, ?_⟩
    · change K.a k + (ρ : ℂ) * (D.E t.val k - K.a k) ∈ (chartAt ℂ (K.x k)).target
      rw [hE k, ← Complex.real_smul]
      exact K.ball_sub k (Convex.add_smul_sub_mem (convex_ball _ _) h0.2 h1.2 hρ)
    · exact (chartAt ℂ (K.x (k + 1))).map_source h0'.1
    · have := (chartAt ℂ (K.x (k + 1))).left_inv h0'.1
      change (b66g_inv R t (a (k + 1)) (K.a (k + 1))).val ∈ (R.atlas.A (a k)).source
      have e1 : b66g_inv R t (a (k + 1)) (K.a (k + 1)) = P ((k + 1 : ℤ) / (N : ℝ)) := this
      rw [e1]
      have hy : P ((k + 1 : ℤ) / (N : ℝ)) = P ((k + 1) / N) := by push_cast; rfl
      rw [hy]
      exact h1.1
  refine ⟨D, hv, ?_⟩
  have hloop : D.loop t = K.loop := by
    funext σ
    change b66g_inv R t (a _) (b66g_segPt (K.a _) (D.E t.val _) _) = _
    rw [hE]
    change _ = (chartAt ℂ (K.x _)).symm (K.a _ + Real.smoothTransition (3 * _ - 1) • (K.b _ - K.a _))
    rw [hch, Complex.real_smul]
    rfl
  rw [b66g_loopClass_eq_cls]
  have hK := b66g_cls_homotopy (X := b66g_RF R t) K.hom (K.continuous_hom hPc)
    (fun s σ => K.hom_periodic hper s σ)
  have key : ∀ (p q : ℝ → rf8_fibre R.C t) (hpq : p = q) (hp hq hp' hq'),
      b66g_cls p hp hp' = b66g_cls q hq hq' := by
    intro p q hpq _ _ _ _
    subst hpq
    rfl
  have e1 : (fun σ => K.hom (1, σ)) = D.loop t := by
    funext σ; rw [K.hom_one, hloop]
  have e0 : (fun σ => K.hom (0, σ)) = P := by
    funext σ; rw [K.hom_zero]
  refine (key _ _ e1.symm _ _ _ _).trans (hK.symm.trans ((key _ _ e0 _ hPc _ hper).trans ?_))
  change ((SingularChainComplex ℤ (TopCat.of (rf8_fibre R.C t))).sc 1).moduleCatHomologyClass
      (loopCycle ℤ ⟨hper.lift, _⟩) = _
  congr 2

/-- Retained polygon classes span the integral homology of a fibre. -/
theorem b66g_poly_span (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule.span ℤ {x : b6m_H1 (rf8_fibre R.C t) | ∃ (D : b66g_Poly R) (hv : D.Valid t),
      x = b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop hv)} = ⊤ := by
  have : LocallyPathConnectedSpace (rf8_fibre R.C t) :=
    ChartedSpace.locallyPathConnectedSpace ℂ _
  have : PathConnectedSpace (rf8_fibre R.C t) := PathConnectedSpace.of_locallyPathConnectedSpace
  apply top_unique
  rw [← b6m_continuous_loops_span (rf8_fibre R.C t)]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  obtain ⟨D, hv, h⟩ := b66g_exists_poly R t p
  have hmem : b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop hv) ∈ Submodule.span ℤ
      {x : b6m_H1 (rf8_fibre R.C t) | ∃ (D : b66g_Poly R) (hv : D.Valid t),
        x = b6m_loopClass (rf8_fibre R.C t) (D.smoothLoop hv)} :=
    Submodule.subset_span ⟨D, hv, rfl⟩
  rw [h] at hmem
  exact hmem

end B66gRetainedAtlas

section B66gValidOpen

namespace b66g_Poly

variable {R : rf8_SharedFamily} (D : b66g_Poly R)

theorem periodic_prop {P : ℤ → Prop} (hP : ∀ k, P (k + D.N) ↔ P k)
    (h : ∀ k ∈ Finset.range D.N, P k) : ∀ k, P k := by
  have hm : ∀ (j : ℤ) (m : ℤ), P (j + m * D.N) ↔ P j := by
    intro j m
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih => rw [add_mul, one_mul, ← add_assoc, hP, ih]
    | pred m ih =>
      rw [← hP, sub_mul, one_mul, add_sub_assoc', sub_add_cancel, ih]
  intro k
  have hN : (0 : ℤ) < D.N := by exact_mod_cast D.pos
  have hk : k % D.N + k / D.N * D.N = k := by
    have := Int.mul_ediv_add_emod k D.N
    linarith [mul_comm (D.N : ℤ) (k / D.N)]
  have h0 : 0 ≤ k % D.N := Int.emod_nonneg k hN.ne'
  have h1 : k % D.N < D.N := Int.emod_lt_of_pos k hN
  have hmem : (k % D.N).toNat ∈ Finset.range D.N := by
    rw [Finset.mem_range]; omega
  have := h _ hmem
  rw [Int.toNat_of_nonneg h0] at this
  rw [← hk, hm]
  exact this

theorem valid_iff_range (u : b6t_polydisc mr_base) :
    D.Valid u ↔ ∀ k ∈ Finset.range D.N,
      b66g_SegIn R u (D.a k) (D.c k) (D.E u.val k) ∧ D.c (k + 1) ∈ b66k_domain R u (D.a (k + 1)) ∧
        (b66g_inv R u (D.a (k + 1)) (D.c (k + 1))).val ∈ (R.atlas.A (D.a k)).source := by
  refine ⟨fun h k _ => h k, fun h => D.periodic_prop (fun k => ?_) h⟩
  simp only [add_right_comm k (D.N : ℤ) 1, D.a_add, D.c_add, D.E_add]

/-- A polygon defined over `t` is defined over every nearby parameter. -/
theorem valid_eventually {t : b6t_polydisc mr_base} (ht : D.Valid t) :
    ∀ᶠ w in 𝓝 t.val, ∃ h : w ∈ b6t_polydisc mr_base, D.Valid ⟨w, h⟩ := by
  have hopen : IsOpen (b6t_polydisc mr_base) := rf5_polydisc_isOpen mr_base
  have hk : ∀ k ∈ Finset.range D.N, ∀ᶠ w in 𝓝 t.val,
      (∀ r ∈ Icc (0 : ℝ) 1, (w, D.c k + (r : ℂ) * (D.E w k - D.c k)) ∈
        (R.atlas.A (D.a k)).target) ∧ (w, D.c (k + 1)) ∈ (R.atlas.A (D.a (k + 1))).target ∧
        (R.atlas.A (D.a (k + 1))).symm (w, D.c (k + 1)) ∈ (R.atlas.A (D.a k)).source := by
    intro k _
    have h1 : (t.val, D.c (k + 1)) ∈ (R.atlas.A (D.a (k + 1))).target := (ht k).2.1
    have h2 : (R.atlas.A (D.a (k + 1))).symm (t.val, D.c (k + 1)) ∈
        (R.atlas.A (D.a k)).source := by
      have := (ht k).2.2
      rwa [b66g_inv_val R t (D.a (k + 1)) (ht k).2.1] at this
    have hE := D.E_continuousAt ht k
    refine ((isCompact_Icc.eventually_forall_of_forall_eventually fun r₀ hr₀ => ?_).and
      (?_ : ∀ᶠ w in 𝓝 t.val, _)).mono fun w hw => ⟨hw.1, hw.2⟩
    · have hE' : ContinuousAt (fun z : (Fin 10 → ℂ) × ℝ => D.E z.1 k) (t.val, r₀) :=
        hE.comp_of_eq (f := fun z : (Fin 10 → ℂ) × ℝ => z.1) continuous_fst.continuousAt rfl
      have hr : ContinuousAt (fun z : (Fin 10 → ℂ) × ℝ => (z.2 : ℂ)) (t.val, r₀) :=
        Complex.continuous_ofReal.continuousAt.comp (f := fun z : (Fin 10 → ℂ) × ℝ => z.2)
          continuous_snd.continuousAt
      have hc : ContinuousAt (fun z : (Fin 10 → ℂ) × ℝ =>
          (z.1, D.c k + (z.2 : ℂ) * (D.E z.1 k - D.c k))) (t.val, r₀) :=
        continuous_fst.continuousAt.prodMk (continuousAt_const.add
          (hr.mul (hE'.sub continuousAt_const)))
      exact hc.preimage_mem_nhds ((R.atlas.A (D.a k)).open_target.mem_nhds ((ht k).1 r₀ hr₀))
    · have hc1 : ContinuousAt (fun w : Fin 10 → ℂ => (w, D.c (k + 1))) t.val :=
        continuous_id.continuousAt.prodMk continuousAt_const
      have ev1 := hc1.preimage_mem_nhds ((R.atlas.A (D.a (k + 1))).open_target.mem_nhds h1)
      have hc2 : ContinuousAt (fun w : Fin 10 → ℂ =>
          (R.atlas.A (D.a (k + 1))).symm (w, D.c (k + 1))) t.val :=
        ((R.atlas.A (D.a (k + 1))).continuousAt_symm h1).comp (f := fun w => (w, D.c (k + 1))) hc1
      have ev2 := hc2.preimage_mem_nhds ((R.atlas.A (D.a k)).open_source.mem_nhds h2)
      exact Filter.Eventually.and ev1 ev2
  have hall := (Filter.eventually_all_finset (Finset.range D.N)).2 hk
  filter_upwards [hall, hopen.mem_nhds t.property] with w hw hwp
  refine ⟨hwp, (D.valid_iff_range _).2 fun k hk => ⟨fun r hr => (hw k hk).1 r hr,
    (hw k hk).2.1, ?_⟩⟩
  rw [b66g_inv_val R ⟨w, hwp⟩ (D.a (k + 1)) (hw k hk).2.1]
  exact (hw k hk).2.2

end b66g_Poly

end B66gValidOpen

end HodgeLean.Foundations.Program
