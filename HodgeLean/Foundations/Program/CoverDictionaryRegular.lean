import HodgeLean.Foundations.Program.CoverDictionaryDefs

/-! # B6-5 stage 5d, geometric part: the regular locus carries enough of `ds`

A non-constant analytic map from a compact connected Riemann surface has finitely many critical
points (local constancy is a clopen condition, and critical points accumulate only where the map is
locally constant, by isolated zeros of the derivative in a chart). Consequently, on every fibre
of a family at the G32 centre, `ds` is nonzero at some tangent vector over a regular point, for
infinitely many values of `s`. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

section Crit
variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
include hf

/-- Near a point, a critical point has vanishing chart derivative. -/
theorem b65g_crit_chart (x : X) : ∀ᶠ x' in 𝓝 x, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x' = 0 →
    deriv (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (extChartAt 𝓘(ℂ, ℂ) x x') = 0 := by
  have h1 : (chartAt ℂ x).source ∈ 𝓝 x := (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have h2 : f ⁻¹' (chartAt ℂ (f x)).source ∈ 𝓝 x :=
    (hf x).continuousAt.preimage_mem_nhds
      ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
  filter_upwards [h1, h2] with x' hx' hfx' h0
  set e := extChartAt 𝓘(ℂ, ℂ) x
  have hxe : x' ∈ e.source := by rwa [extChartAt_source]
  have hy : e x' ∈ e.target := e.map_source hxe
  have hsymm : e.symm (e x') = x' := e.left_inv hxe
  have hd1 : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e x')
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e x')) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) hy
    simp only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at this
    exact this.hasMFDerivAt
  have hd2 : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f (e.symm (e x')) 0 := by
    rw [hsymm, ← h0]
    exact ((hf x').mdifferentiableAt (by simp)).hasMFDerivAt
  have hd3 : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (f x)) (f (e.symm (e x')))
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (f x)) (f (e.symm (e x')))) := by
    rw [hsymm]; exact (mdifferentiableAt_extChartAt hfx').hasMFDerivAt
  have hc := hd3.comp (e x') (hd2.comp (e x') hd1)
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] at hc
  have hF : HasFDerivAt (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (0 : ℂ →L[ℂ] ℂ) (e x') :=
    hasMFDerivAt_iff_hasFDerivAt.mp hc
  simpa using hF.hasDerivAt.deriv

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- An analytic map is analytic in charts. -/
theorem b65g_chart_analytic (x : X) :
    AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (extChartAt 𝓘(ℂ, ℂ) x x) := by
  have h := ((contMDiffAt_iff).mp (hf x)).2
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h
  exact h.analyticAt

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Vanishing chart derivative near a point makes the map locally constant there. -/
theorem b65g_const_of_chart (x : X)
    (h : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
      deriv (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) y = 0) :
    ∀ᶠ x' in 𝓝 x, f x' = f x := by
  set F := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f
  set e := extChartAt 𝓘(ℂ, ℂ) x
  have ha := (b65g_chart_analytic hf x).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (ha.and h)
  have hconst : ∀ y ∈ Metric.ball (e x) r, F y = F (e x) := fun y hy ↦
    IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (fun z hz ↦ (hball z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hball z hz).2) hy (Metric.mem_ball_self hr)
  have h1 : (chartAt ℂ x).source ∈ 𝓝 x := (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have h2 : f ⁻¹' (chartAt ℂ (f x)).source ∈ 𝓝 x :=
    (hf x).continuousAt.preimage_mem_nhds
      ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
  have h3 : e ⁻¹' Metric.ball (e x) r ∈ 𝓝 x :=
    (continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  filter_upwards [h1, h2, h3] with x' hx' hfx' hb
  have hxe : x' ∈ e.source := by rwa [extChartAt_source]
  have hfe : f x' ∈ (extChartAt 𝓘(ℂ, ℂ) (f x)).source := by rwa [extChartAt_source]
  have hfx : f x ∈ (extChartAt 𝓘(ℂ, ℂ) (f x)).source := mem_extChartAt_source _
  have hk : extChartAt 𝓘(ℂ, ℂ) (f x) (f (e.symm (e x'))) =
      extChartAt 𝓘(ℂ, ℂ) (f x) (f (e.symm (e x))) := hconst _ hb
  rw [e.left_inv hxe, e.left_inv (mem_extChartAt_source x)] at hk
  exact (extChartAt 𝓘(ℂ, ℂ) (f x)).injOn hfe hfx hk

/-- At an accumulation point of critical points the map is locally constant. -/
theorem b65g_local_const_of_accPt (x : X)
    (hx : AccPt x (𝓟 {x' | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x' = 0})) :
    ∀ᶠ x' in 𝓝 x, f x' = f x := by
  refine b65g_const_of_chart hf x ?_
  refine ((b65g_chart_analytic hf x).deriv).frequently_zero_iff_eventually_zero.mp ?_
  intro hne
  rw [eventually_nhdsWithin_iff] at hne
  have hne' := (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) x).eventually hne
  have h1 : (chartAt ℂ x).source ∈ 𝓝 x := (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  rw [accPt_iff_frequently] at hx
  obtain ⟨y, ⟨hyx, hy⟩, hk, hn, hs⟩ :=
    (hx.and_eventually ((b65g_crit_chart hf x).and (hne'.and h1))).exists
  have hye : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source := by rwa [extChartAt_source]
  have hne2 : extChartAt 𝓘(ℂ, ℂ) x y ≠ extChartAt 𝓘(ℂ, ℂ) x x := fun h ↦
    hyx ((extChartAt 𝓘(ℂ, ℂ) x).injOn hye (mem_extChartAt_source x) h)
  exact hn hne2 (hk hy)

/-- **Finitely many critical points.** A non-constant analytic map from a compact connected
Riemann surface has finitely many critical points. -/
theorem b65g_crit_finite [CompactSpace X] [ConnectedSpace X] (hnc : ∃ x y, f x ≠ f y) :
    {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0}.Finite := by
  set Z := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0}
  set L := {x | ∀ᶠ x' in 𝓝 x, f x' = f x}
  have hLZ : L ⊆ Z := fun x hx ↦
    ((hasMFDerivAt_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (f x) x).congr_of_eventuallyEq hx).mfderiv
  have hopen : IsOpen L := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hx.eventually_nhds, hx] with y hy hyx
    exact hy.mono fun z hz ↦ hz.trans hyx.symm
  have hclosed : IsClosed L := by
    refine isClosed_of_closure_subset fun x hx ↦ ?_
    by_contra hxL
    have hacc : AccPt x (𝓟 L) := by
      rw [accPt_iff_frequently]
      exact (mem_closure_iff_frequently.mp hx).mono fun y hy ↦ ⟨fun h ↦ hxL (h ▸ hy), hy⟩
    exact hxL (b65g_local_const_of_accPt hf x (hacc.mono (principal_mono.mpr hLZ)))
  by_contra hZ
  obtain ⟨x, hx⟩ := Set.Infinite.exists_accPt_principal hZ
  have hL : L = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x, b65g_local_const_of_accPt hf x hx⟩
  have hlc : IsLocallyConstant f :=
    (IsLocallyConstant.iff_eventually_eq f).mpr fun x ↦ (hL ▸ mem_univ x : x ∈ L)
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (hlc.apply_eq_of_preconnectedSpace a b)

end Crit


attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The `s`-coordinate has injective derivative at a finite point with finite image. -/
theorem b65g_sCoord_hasMFDerivAt {a b z : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (hz : b - z * (b - a) ≠ 0) (p : OnePoint ℂ) (hp : p = (z : OnePoint ℂ)) :
    ∃ L : ℂ →L[ℂ] ℂ, HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sCoord a b) p L ∧
      Function.Injective L := by
  subst hp
  set h : ℂ → ℂ := fun w ↦ a * b / (b - w * (b - a))
  have hh : HasDerivAt h (a * b * (b - a) / (b - z * (b - a)) ^ 2) z := by
    have := (hasDerivAt_const z (a * b)).div ((hasDerivAt_const z b).sub
      ((hasDerivAt_id z).mul_const (b - a))) hz
    convert this using 1
    · funext w; simp [h]
    · simp only [Pi.sub_apply, id]; ring
  have hh0 : a * b * (b - a) / (b - z * (b - a)) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hab hba) (pow_ne_zero 2 hz)
  have hz0 : extChartAt 𝓘(ℂ, ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ) = z := by
    simp [b4cov_chartAt_coe, b4cov_chart0_coe]
  have hE := (mdifferentiableAt_extChartAt (I := 𝓘(ℂ, ℂ))
    (mem_chart_source ℂ (z : OnePoint ℂ))).hasMFDerivAt
  have hinv := isInvertible_mfderiv_extChartAt (I := 𝓘(ℂ, ℂ))
    (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) (z : OnePoint ℂ))
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) h (extChartAt 𝓘(ℂ, ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ))
      ((1 : ℂ →L[ℂ] ℂ).smulRight (a * b * (b - a) / (b - z * (b - a)) ^ 2)) := by
    rw [hz0]; exact hasMFDerivAt_iff_hasFDerivAt.mpr hh.hasFDerivAt
  refine ⟨_, (hH.comp (z : OnePoint ℂ) hE).congr_of_eventuallyEq_abuse ?_, ?_⟩
  · filter_upwards [OnePoint.isOpen_range_coe.mem_nhds (mem_range_self z)] with p hp
    obtain ⟨w, rfl⟩ := hp
    simp [h, b65g_sCoord, b4cov_chartAt_coe, b4cov_chart0_coe]
  · intro v w hvw
    have h1 : @id ℂ (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (z : OnePoint ℂ)) (z : OnePoint ℂ) v) *
        (a * b * (b - a) / (b - z * (b - a)) ^ 2) =
        @id ℂ (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (z : OnePoint ℂ)) (z : OnePoint ℂ) w) *
        (a * b * (b - a) / (b - z * (b - a)) ^ 2) := hvw
    obtain ⟨M, hM⟩ := hinv
    have h2 := mul_right_cancel₀ hh0 h1
    rw [← hM] at h2
    exact M.injective h2


attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- At a regular point that is not critical for the projection, `ds` is nonzero. -/
theorem b65g_ds_ne {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0) (x : b65z_fibre c D.C t)
    (z : ℂ) (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x = z)
    (hz : b - z * (b - a) ≠ 0)
    (hcrit : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t) x ≠ 0) :
    ∃ w, b65g_ds D t a b ⟨x, w⟩ ≠ 0 := by
  obtain ⟨L, hL, hinj⟩ := b65g_sCoord_hasMFDerivAt hab hba hz _ hx
  have hP := ((D.hk t x).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) x = L.comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t) x) :=
    (hL.comp x hP).mfderiv
  obtain ⟨w, hw⟩ : ∃ w, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t) x w ≠ 0 := by
    by_contra h
    exact hcrit (ContinuousLinearMap.ext fun w ↦ by_contra fun hw ↦ h ⟨w, hw⟩)
  refine ⟨w, ?_⟩
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) x w ≠ 0
  rw [hc]
  exact fun h ↦ hw (hinj (h.trans (map_zero L).symm))

/-- The `s`-coordinate is injective on the finite points. -/
theorem b65g_sCoord_injective {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0) :
    Function.Injective fun z : ℂ ↦ b65g_sCoord a b (z : OnePoint ℂ) := by
  intro z z' h
  have h' : a * b / (b - z * (b - a)) = a * b / (b - z' * (b - a)) := h
  rw [div_eq_mul_inv, div_eq_mul_inv] at h'
  have := inv_injective (mul_left_cancel₀ hab h')
  exact mul_right_cancel₀ hba (by linear_combination -this)

/-- **Rich regular locus.** Over infinitely many values of `s` there is a regular point and a
tangent vector on which `ds` does not vanish. -/
theorem b65g_rich {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    {s : ℂ | ∃ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t),
      u.1 ∈ b65g_good D t a b poles ∧ b65g_sFun D t a b u.1 = s ∧ b65g_ds D t a b u ≠ 0}.Infinite := by
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  have hnc : ∃ x y, π x ≠ π y := by
    obtain ⟨x, hx⟩ := D.hsurj t OnePoint.infty
    obtain ⟨y, hy⟩ := D.hsurj t ((0 : ℂ) : OnePoint ℂ)
    exact ⟨x, y, fun h ↦ OnePoint.infty_ne_coe 0 (hx.symm.trans (h.trans hy))⟩
  have hZ := b65g_crit_finite (D.hk t) hnc
  set Z := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) π x = 0}
  set B : Set ℂ := {z | b - z * (b - a) = 0} ∪
    ((fun z : ℂ ↦ b65g_sCoord a b (z : OnePoint ℂ)) ⁻¹' Set.range poles ∪
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' (π '' Z))
  have hB : B.Finite := by
    refine Set.Finite.union ?_ (Set.Finite.union ?_ ?_)
    · refine (Set.finite_singleton (b / (b - a))).subset fun z hz ↦ ?_
      simp only [mem_ofPred_eq] at hz
      simp only [mem_singleton_iff]
      field_simp
      linear_combination -hz
    · exact (Set.finite_range poles).preimage (b65g_sCoord_injective hab hba).injOn
    · exact (hZ.image π).preimage (OnePoint.coe_injective.injOn)
  refine ((hB.infinite_compl).image (b65g_sCoord_injective hab hba).injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  simp only [B, mem_compl_iff, mem_union, mem_ofPred_eq, mem_preimage, not_or] at hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨x, hx⟩ := D.hsurj t (z : OnePoint ℂ)
  have hxZ : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) π x ≠ 0 := fun h ↦ hz3 ⟨x, h, hx⟩
  obtain ⟨w, hw⟩ := b65g_ds_ne D t hab hba x z hx hz1 hxZ
  exact ⟨⟨x, w⟩, ⟨z, hx, hz1, hz2⟩, by simp [b65g_sFun, hx], hw⟩

end HodgeLean.Foundations.Program
