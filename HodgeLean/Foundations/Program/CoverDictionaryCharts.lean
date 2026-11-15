import HodgeLean.Foundations.Program.CoverDictionaryOrders
import HodgeLean.Foundations.Program.CoverDictionarySolutions

/-! # B6-5 stage 5d, stage four: the `s`-function in charts of a fibre

On a fibre of a family, in the chart at a point `x`: the projection is analytic and not locally
constant; at a point over a finite `s` the `s`-function is analytic, and it is `s(x) + κᵉ` for a
local parameter `κ` with a simple zero (`b65g_sFun_root`); at a point over `s = ∞` its inverse is
`κᵉ` (`b65g_sFun_root_infty`). Where the `s`-function is injective near `x` (on the regular locus,
by the covering of stage three) its chart derivative does not vanish (`b65g_chart_deriv_ne`).
Derivatives on the fibre are derivatives in the chart (`caf_hasDerivAt_chart`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

section General

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Derivatives in a chart.** A function on a surface with manifold derivative `L` at
`φ⁻¹ z` has derivative `L (dφ⁻¹ 1)` at `z` in the chart `φ` at `x`. -/
theorem caf_hasDerivAt_chart (x : M) (f : M → F) (z : ℂ)
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) (L : ℂ →L[ℂ] F)
    (hf : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, F) f ((extChartAt 𝓘(ℂ, ℂ) x).symm z) L) :
    HasDerivAt (fun w ↦ f ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
      (L (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ))) z := by
  have hd1 : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) hz
    simp only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at this
    exact this.hasMFDerivAt
  have hc := hf.comp z hd1
  have hF : HasFDerivAt (fun w ↦ f ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
      (L.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z)) z :=
    hasMFDerivAt_iff_hasFDerivAt.mp hc
  exact hF.hasDerivAt

omit [IsManifold 𝓘(ℂ, ℂ) ω M] in
/-- In a surface, a point is not isolated: a finite set is never a neighbourhood. -/
theorem caf_not_finite_nhds [T2Space M] (x : M) (S : Set M) (hS : S.Finite) : S ∉ 𝓝 x := by
  intro hSx
  have hne := caf_nhdsNE_neBot x
  have h1 : (S \ {x})ᶜ ∈ 𝓝 x :=
    (hS.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have h2 : (∅ : Set M) ∈ 𝓝[≠] x := by
    filter_upwards [nhdsWithin_le_nhds hSx, nhdsWithin_le_nhds h1, self_mem_nhdsWithin]
      with y hy1 hy2 hy3
    exact hy2 ⟨hy1, hy3⟩
  exact hne.ne (empty_mem_iff_bot.mp h2)

end General

/-- **Composition with a local biholomorphism keeps non-constancy.** -/
theorem caf_not_const_comp (h P : ℂ → ℂ) (z₀ : ℂ) (hh : AnalyticAt ℂ h (P z₀))
    (hh' : deriv h (P z₀) ≠ 0) (hP : ContinuousAt P z₀) (hnc : ¬ EventuallyConst P (𝓝 z₀)) :
    ¬ EventuallyConst (fun z ↦ h (P z)) (𝓝 z₀) := by
  intro hc
  apply hnc
  have hs := hh.hasStrictDerivAt
  have hinv := hs.eventually_left_inverse hh'
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.mp hc
  refine eventuallyConst_iff_exists_eventuallyEq.mpr ⟨hs.localInverse h _ _ hh' c, ?_⟩
  filter_upwards [hP.eventually hinv, hc] with z hz1 hz2
  rw [← hz1]
  exact congrArg _ hz2

section Fibre

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c)

/-- **The projection in charts.** The projection written in the charts at `x` and `π x` is
analytic, and near the chart value of `x` the projection of `φ⁻¹ z` is the inverse chart of the
written projection. -/
theorem b65g_proj_chart (x : b65z_fibre c D.C t) :
    AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t))
        (extChartAt 𝓘(ℂ, ℂ) x x) ∧
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
      b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
        (extChartAt 𝓘(ℂ, ℂ) (b63d_projection c D.C D.atlas.f (b6t_polydisc c)
          (Subset.refl _) t x)).symm (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x
            (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t) z) := by
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  refine ⟨b65g_chart_analytic (D.hk t) x, ?_⟩
  have hcont : ContinuousAt (fun z ↦ π ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
    refine ContinuousAt.comp (f := (extChartAt 𝓘(ℂ, ℂ) x).symm) (g := π) ?_
      (continuousAt_extChartAt_symm x)
    rw [extChartAt_to_inv]
    exact (D.hk t).continuous.continuousAt
  have hsrc : (extChartAt 𝓘(ℂ, ℂ) (π x)).source ∈ 𝓝 (π x) :=
    extChartAt_source_mem_nhds (π x)
  have := hcont.preimage_mem_nhds (by rw [extChartAt_to_inv]; exact hsrc)
  filter_upwards [this] with z hz
  simp only [writtenInExtChartAt, Function.comp_apply]
  exact ((extChartAt 𝓘(ℂ, ℂ) (π x)).left_inv hz).symm

variable {a b : ℂ}

/-- The `s`-coordinate in the chart at infinity of the sphere. -/
theorem b65g_sCoord_sphInv (w : ℂ) :
    b65g_sCoord a b (b4cov_sphInv (w : OnePoint ℂ)) = a * b * w / (b * w - (b - a)) := by
  by_cases hw : w = 0
  · subst hw
    rw [b4cov_sphInv_zero]
    simp [b65g_sCoord]
  · rw [b4cov_sphInv_coe hw]
    change a * b / (b - w⁻¹ * (b - a)) = _
    rw [show b - w⁻¹ * (b - a) = (b * w - (b - a)) / w by field_simp, div_div_eq_mul_div]

/-- The inverse of the `s`-coordinate at a finite point. -/
theorem b65g_sCoord_inv (w : ℂ) :
    (b65g_sCoord a b (w : OnePoint ℂ))⁻¹ = (b - w * (b - a)) / (a * b) := by
  change (a * b / (b - w * (b - a)))⁻¹ = _
  rw [inv_div]

/-- The written projection at `x` takes the chart value of `π x` at the chart value of `x`. -/
theorem b65g_proj_chart_center (x : b65z_fibre c D.C t) :
    writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x
        (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t)
        (extChartAt 𝓘(ℂ, ℂ) x x) =
      extChartAt 𝓘(ℂ, ℂ) (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x)
        (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x) := by
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]

/-- **The `s`-function is analytic in charts** at every point over a finite `s`. -/
theorem b65g_sFun_chart_analytic (hba : b - a ≠ 0) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ)) :
    AnalyticAt ℂ (fun z ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
  obtain ⟨hP, hev⟩ := b65g_proj_chart D t x
  have hc := b65g_proj_chart_center D t x
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set P := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x π
  cases hpx : π x with
  | infty =>
    have hP0 : P (extChartAt 𝓘(ℂ, ℂ) x x) = 0 := by
      rw [hc, hpx]
      simp [b4cov_chartAt_infty, b4cov_chartInf_apply, b4cov_sphInv]
      exact b4cov_chart0_coe 0
    have hh : AnalyticAt ℂ (fun w ↦ a * b * w / (b * w - (b - a))) (P (extChartAt 𝓘(ℂ, ℂ) x x)) := by
      rw [hP0]
      refine (analyticAt_const.mul analyticAt_id).div (analyticAt_const.mul analyticAt_id |>.sub
        analyticAt_const) ?_
      simp only [mul_zero, zero_sub, neg_ne_zero]
      exact hba
    refine (hh.comp hP).congr ?_
    filter_upwards [hev] with z hz
    simp only [b65g_sFun, Function.comp_apply]
    change _ = b65g_sCoord a b (π _)
    rw [hz, hpx]
    simp only [extChartAt_coe_symm, b4cov_chartAt_infty, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq, b4cov_chartInf_symm, b65g_sCoord_sphInv]
  | coe w₀ =>
    have hP0 : P (extChartAt 𝓘(ℂ, ℂ) x x) = w₀ := by
      rw [hc, hpx]
      simp only [extChartAt_coe, b4cov_chartAt_coe, modelWithCornersSelf_coe, Function.comp_apply,
        id_eq]
      exact b4cov_chart0_coe w₀
    have hw₀ : b - w₀ * (b - a) ≠ 0 := by
      intro h
      apply hx
      rw [hpx]
      congr 1
      field_simp
      linear_combination -h
    have hh : AnalyticAt ℂ (fun w ↦ a * b / (b - w * (b - a))) (P (extChartAt 𝓘(ℂ, ℂ) x x)) := by
      rw [hP0]
      exact analyticAt_const.div (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)) hw₀
    refine (hh.comp hP).congr ?_
    filter_upwards [hev] with z hz
    simp only [b65g_sFun, Function.comp_apply]
    change _ = b65g_sCoord a b (π _)
    rw [hz, hpx]
    simp only [extChartAt_coe_symm, b4cov_chartAt_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq, b4cov_chart0_symm]
    rfl


/-- **The inverse `s`-function at a point over `s = ∞`** is analytic in the chart and vanishes
at the point. -/
theorem b65g_sFun_chart_inv (hab : a * b ≠ 0) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x =
      ((b / (b - a) : ℂ) : OnePoint ℂ)) (hba : b - a ≠ 0) :
    AnalyticAt ℂ (fun z ↦ (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹)
      (extChartAt 𝓘(ℂ, ℂ) x x) ∧
    (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm (extChartAt 𝓘(ℂ, ℂ) x x)))⁻¹ = 0 := by
  obtain ⟨hP, hev⟩ := b65g_proj_chart D t x
  have hc := b65g_proj_chart_center D t x
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set P := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x π
  refine ⟨?_, ?_⟩
  · have hh : AnalyticAt ℂ (fun w ↦ (b - w * (b - a)) / (a * b)) (P (extChartAt 𝓘(ℂ, ℂ) x x)) :=
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div analyticAt_const hab
    refine (hh.comp hP).congr ?_
    filter_upwards [hev] with z hz
    simp only [b65g_sFun, Function.comp_apply]
    change _ = (b65g_sCoord a b (π _))⁻¹
    rw [hz, hx]
    simp only [extChartAt_coe_symm, b4cov_chartAt_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq, b4cov_chart0_symm, b65g_sCoord_inv]
  · simp only [b65g_sFun, extChartAt_to_inv]
    change (b65g_sCoord a b (π x))⁻¹ = 0
    rw [hx, b65g_sCoord_inv, div_mul_cancel₀ _ hba, sub_self, zero_div]

/-- **The projection is not locally constant** in any chart. -/
theorem b65g_proj_chart_not_const (x : b65z_fibre c D.C t) :
    ¬ EventuallyConst (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t))
        (𝓝 (extChartAt 𝓘(ℂ, ℂ) x x)) := by
  obtain ⟨hP, hev⟩ := b65g_proj_chart D t x
  have hc := b65g_proj_chart_center D t x
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set P := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x π
  intro hconst
  obtain ⟨w, hw⟩ := eventuallyConst_iff_exists_eventuallyEq.mp hconst
  have hnc : ∃ x y, π x ≠ π y := by
    obtain ⟨x₁, hx₁⟩ := D.hsurj t OnePoint.infty
    obtain ⟨x₂, hx₂⟩ := D.hsurj t ((0 : ℂ) : OnePoint ℂ)
    exact ⟨x₁, x₂, fun h ↦ OnePoint.infty_ne_coe 0 (hx₁.symm.trans (h.trans hx₂))⟩
  have hfin := b65g_crit_finite (D.hk t) hnc
  -- `π` is constant near `x`
  have hloc : ∀ᶠ y in 𝓝 x, π y = π x := by
    have h1 : ∀ᶠ y in 𝓝 x, extChartAt 𝓘(ℂ, ℂ) x y ∈ {z | π ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
        (extChartAt 𝓘(ℂ, ℂ) (π x)).symm (P z) ∧ P z = w} :=
      (continuousAt_extChartAt x).preimage_mem_nhds (hev.and hw)
    have h0 : P (extChartAt 𝓘(ℂ, ℂ) x x) = w := hw.self_of_nhds
    filter_upwards [h1, extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) x] with y ⟨hy1, hy2⟩ hys
    rw [(extChartAt 𝓘(ℂ, ℂ) x).left_inv hys] at hy1
    rw [hy1, hy2, ← h0, hc, (extChartAt 𝓘(ℂ, ℂ) (π x)).left_inv (mem_extChartAt_source _)]
  have hcrit : {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) π y = 0} ∈ 𝓝 x := by
    obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp hloc
    filter_upwards [hUo.mem_nhds hxU] with y hy
    have hy' : π =ᶠ[𝓝 y] fun _ ↦ π x :=
      Filter.eventually_of_mem (hUo.mem_nhds hy) fun z hz ↦ hU hz
    exact ((hasMFDerivAt_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (π x) y).congr_of_eventuallyEq
      hy').mfderiv
  exact caf_not_finite_nhds x _ hfin hcrit

/-- **Root form of the `s`-function** at a point over a finite `s`: in the chart at `x`,
`s = s(x) + κᵉ` near the chart value, with `κ = (z − z₀) l`, `l(z₀) ≠ 0`. -/
theorem b65g_sFun_root (hab : a * b ≠ 0) (hba : b - a ≠ 0) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ)) :
    ∃ e : ℕ, 0 < e ∧ ∃ l : ℂ → ℂ, AnalyticAt ℂ l (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      l (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
        b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
          b65g_sFun D t a b x + ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ e := by
  obtain ⟨hP, hev⟩ := b65g_proj_chart D t x
  have hc := b65g_proj_chart_center D t x
  have hnc0 := b65g_proj_chart_not_const D t x
  have han := b65g_sFun_chart_analytic D t hba x hx
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set P := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x π
  set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
  have hnc : ¬ EventuallyConst (fun z ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (𝓝 z₀) := by
    cases hpx : π x with
    | infty =>
      have hP0 : P z₀ = 0 := by
        rw [hc, hpx]
        simp [b4cov_chartAt_infty, b4cov_chartInf_apply, b4cov_sphInv]
        exact b4cov_chart0_coe 0
      have hd : HasDerivAt (fun w ↦ a * b * w / (b * w - (b - a))) (-(a * b) / (b - a)) 0 := by
        have h1 : HasDerivAt (fun w : ℂ ↦ a * b * w) (a * b) 0 := by
          simpa using (hasDerivAt_id (0 : ℂ)).const_mul (a * b)
        have h2 : HasDerivAt (fun w : ℂ ↦ b * w - (b - a)) b 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).sub_const (b - a)
        have h0 : b * 0 - (b - a) = -(b - a) := by ring
        have h3 := h1.div h2 (by rw [h0]; exact neg_ne_zero.mpr hba)
        convert h3 using 1
        rw [h0]
        field_simp
        ring
      have hh : AnalyticAt ℂ (fun w ↦ a * b * w / (b * w - (b - a))) (P z₀) := by
        rw [hP0]
        refine (analyticAt_const.mul analyticAt_id).div (analyticAt_const.mul analyticAt_id |>.sub
          analyticAt_const) ?_
        simp only [mul_zero, zero_sub, neg_ne_zero]
        exact hba
      have hh' : deriv (fun w ↦ a * b * w / (b * w - (b - a))) (P z₀) ≠ 0 := by
        rw [hP0, hd.deriv]
        exact div_ne_zero (neg_ne_zero.mpr hab) hba
      have := caf_not_const_comp _ P z₀ hh hh' hP.continuousAt hnc0
      refine fun hk ↦ this (hk.congr ?_)
      filter_upwards [hev] with z hz
      simp only [b65g_sFun]
      change b65g_sCoord a b (π _) = _
      rw [hz, hpx]
      simp only [extChartAt_coe_symm, b4cov_chartAt_infty, modelWithCornersSelf_coe_symm,
        Function.comp_apply, id_eq, b4cov_chartInf_symm, b65g_sCoord_sphInv]
    | coe w₀ =>
      have hP0 : P z₀ = w₀ := by
        rw [hc, hpx]
        simp only [extChartAt_coe, b4cov_chartAt_coe, modelWithCornersSelf_coe,
          Function.comp_apply, id_eq]
        exact b4cov_chart0_coe w₀
      have hw₀ : b - w₀ * (b - a) ≠ 0 := by
        intro h
        apply hx
        rw [hpx]
        congr 1
        field_simp
        linear_combination -h
      have hd : HasDerivAt (fun w ↦ a * b / (b - w * (b - a)))
          (a * b * (b - a) / (b - w₀ * (b - a)) ^ 2) w₀ := by
        have h2 : HasDerivAt (fun w : ℂ ↦ b - w * (b - a)) (-(b - a)) w₀ := by
          simpa using ((hasDerivAt_id w₀).mul_const (b - a)).const_sub b
        have h3 := (hasDerivAt_const w₀ (a * b)).div h2 hw₀
        convert h3 using 1
        ring
      have hh : AnalyticAt ℂ (fun w ↦ a * b / (b - w * (b - a))) (P z₀) := by
        rw [hP0]
        exact analyticAt_const.div (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)) hw₀
      have hh' : deriv (fun w ↦ a * b / (b - w * (b - a))) (P z₀) ≠ 0 := by
        rw [hP0, hd.deriv]
        exact div_ne_zero (mul_ne_zero hab hba) (pow_ne_zero 2 hw₀)
      have := caf_not_const_comp _ P z₀ hh hh' hP.continuousAt hnc0
      refine fun hk ↦ this (hk.congr ?_)
      filter_upwards [hev] with z hz
      simp only [b65g_sFun]
      change b65g_sCoord a b (π _) = _
      rw [hz, hpx]
      simp only [extChartAt_coe_symm, b4cov_chartAt_coe, modelWithCornersSelf_coe_symm,
        Function.comp_apply, id_eq, b4cov_chart0_symm]
      rfl
  obtain ⟨e, he, -, l, hl, hl0, hfl⟩ := caf_root_factor _ z₀ han hnc
  refine ⟨e, he, l, hl, hl0, ?_⟩
  filter_upwards [hfl] with z hz
  rw [hz]
  simp only [z₀, extChartAt_to_inv]

/-- **Root form at a point over `s = ∞`**: in the chart at `x`, `1/s = κᵉ`. -/
theorem b65g_sFun_root_infty (hab : a * b ≠ 0) (hba : b - a ≠ 0) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x =
      ((b / (b - a) : ℂ) : OnePoint ℂ)) :
    ∃ e : ℕ, 0 < e ∧ ∃ l : ℂ → ℂ, AnalyticAt ℂ l (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      l (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
        (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹ =
          ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ e := by
  obtain ⟨hP, hev⟩ := b65g_proj_chart D t x
  have hc := b65g_proj_chart_center D t x
  have hnc0 := b65g_proj_chart_not_const D t x
  obtain ⟨han, hzero⟩ := b65g_sFun_chart_inv D t hab x hx hba
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set P := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x π
  set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
  have hP0 : P z₀ = b / (b - a) := by
    rw [hc, hx]
    simp only [extChartAt_coe, b4cov_chartAt_coe, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq]
    exact b4cov_chart0_coe _
  have hnc : ¬ EventuallyConst (fun z ↦ (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹)
      (𝓝 z₀) := by
    have hd : HasDerivAt (fun w ↦ (b - w * (b - a)) / (a * b)) (-(b - a) / (a * b))
        (P z₀) := by
      have h2 : HasDerivAt (fun w : ℂ ↦ b - w * (b - a)) (-(b - a)) (P z₀) := by
        simpa using ((hasDerivAt_id (P z₀)).mul_const (b - a)).const_sub b
      exact h2.div_const _
    have hh : AnalyticAt ℂ (fun w ↦ (b - w * (b - a)) / (a * b)) (P z₀) :=
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div analyticAt_const hab
    have hh' : deriv (fun w ↦ (b - w * (b - a)) / (a * b)) (P z₀) ≠ 0 := by
      rw [hd.deriv]
      exact div_ne_zero (neg_ne_zero.mpr hba) hab
    have := caf_not_const_comp _ P z₀ hh hh' hP.continuousAt hnc0
    refine fun hk ↦ this (hk.congr ?_)
    filter_upwards [hev] with z hz
    simp only [b65g_sFun]
    change (b65g_sCoord a b (π _))⁻¹ = _
    rw [hz, hx]
    simp only [extChartAt_coe_symm, b4cov_chartAt_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq, b4cov_chart0_symm, b65g_sCoord_inv]
  obtain ⟨e, he, -, l, hl, hl0, hfl⟩ := caf_root_factor _ z₀ han hnc
  refine ⟨e, he, l, hl, hl0, ?_⟩
  filter_upwards [hfl] with z hz
  rw [hz, hzero, zero_add]

/-- **The punctured chart disc lies in the regular locus.** -/
theorem b65g_chart_punctured_good (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (x : b65z_fibre c D.C t) :
    ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x), z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target ∧
      (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈ b65g_good D t a b poles := by
  set φ := extChartAt 𝓘(ℂ, ℂ) x
  set F := (b65g_good D t a b poles)ᶜ
  have hF : F.Finite := b65g_good_compl_finite D t hab hba poles
  have htarget : φ.target ∈ 𝓝 (φ x) :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hFx : (F \ {x})ᶜ ∈ 𝓝 x :=
    (hF.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hsymm : ∀ᶠ z in 𝓝 (φ x), φ.symm z ∈ (F \ {x})ᶜ := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x).tendsto
    rw [extChartAt_to_inv] at this
    exact this hFx
  filter_upwards [nhdsWithin_le_nhds htarget, nhdsWithin_le_nhds hsymm, self_mem_nhdsWithin]
    with z hz h1 h2
  refine ⟨hz, ?_⟩
  by_contra hF'
  refine h1 ⟨hF', fun hzx ↦ h2 ?_⟩
  rw [← φ.right_inv hz, show φ.symm z = x from hzx]
  rfl

/-- **`ds` in a chart**: at `φ⁻¹ z` where the `s`-function is differentiable, `ds` of the chart
vector `∂/∂z` is the derivative of the `s`-function in the chart. -/
theorem b65g_ds_chart (a b : ℂ) (x : b65z_fibre c D.C t) (z : ℂ)
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target)
    (hs : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) :
    HasDerivAt (fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
      (b65g_ds D t a b ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) z :=
  caf_hasDerivAt_chart x _ z hz _ hs.hasMFDerivAt

/-- **Non-vanishing of the chart derivative** where the `s`-function is injective near `x`. -/
theorem b65g_chart_deriv_ne (hab : a * b ≠ 0) (hba : b - a ≠ 0) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ))
    (hinj : ∃ U ∈ 𝓝 x, Set.InjOn (b65g_sFun D t a b) U) :
    deriv (fun z ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 := by
  obtain ⟨e, he, l, hl, hl0, hfl⟩ := b65g_sFun_root D t hab hba x hx
  set φ := extChartAt 𝓘(ℂ, ℂ) x
  set z₀ := φ x
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκd : HasDerivAt κ (l z₀) z₀ := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    exact h
  have he1 : e = 1 := by
    by_contra hne
    have he2 : 2 ≤ e := by omega
    obtain ⟨U, hU, hinjU⟩ := hinj
    have hV : ∀ᶠ z in 𝓝 z₀, (b65g_sFun D t a b (φ.symm z) = b65g_sFun D t a b x + κ z ^ e) ∧
        φ.symm z ∈ U ∧ z ∈ φ.target := by
      have hA : ∀ᶠ z in 𝓝 z₀, φ.symm z ∈ U :=
        (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x).preimage_mem_nhds
          (by rw [extChartAt_to_inv]; exact hU)
      have hB : ∀ᶠ z in 𝓝 z₀, z ∈ φ.target :=
        (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
      exact hfl.and (hA.and hB)
    have hstrict : HasStrictDerivAt κ (l z₀) z₀ := by
      have hκa : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
      have := hκa.hasStrictDerivAt
      rwa [hκd.deriv] at this
    have hmap := hstrict.map_nhds_eq hl0
    have hκ0 : κ z₀ = 0 := by simp [κ]
    rw [hκ0] at hmap
    have hV' : κ '' {z | (b65g_sFun D t a b (φ.symm z) = b65g_sFun D t a b x + κ z ^ e) ∧
        φ.symm z ∈ U ∧ z ∈ φ.target} ∈ 𝓝 (0 : ℂ) := by
      rw [← hmap]
      exact image_mem_map hV
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV'
    set ζ := Complex.exp (2 * Real.pi * Complex.I / e)
    have hζ : IsPrimitiveRoot ζ e := Complex.isPrimitiveRoot_exp e (by omega)
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
    set y : ℂ := ((δ / 2 : ℝ) : ℂ)
    have hy0 : y ≠ 0 := by simp [y, hδ.ne']
    have hy : y ∈ ball (0 : ℂ) δ := by
      simp [y, abs_of_pos hδ]
      linarith
    have hζy : ζ * y ∈ ball (0 : ℂ) δ := by
      have hn : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
      simpa [norm_mul, hn] using hy
    obtain ⟨z₁, ⟨h11, h12, h13⟩, hz₁⟩ := hball hy
    obtain ⟨z₂, ⟨h21, h22, h23⟩, hz₂⟩ := hball hζy
    have hne : z₁ ≠ z₂ := by
      intro h
      rw [h, hz₂] at hz₁
      apply hζ1
      have := mul_right_cancel₀ hy0 (hz₁.trans (one_mul y).symm)
      exact this
    have hseq : b65g_sFun D t a b (φ.symm z₁) = b65g_sFun D t a b (φ.symm z₂) := by
      rw [h11, h21, hz₁, hz₂, mul_pow, hζ.pow_eq_one, one_mul]
    have := hinjU h12 h22 hseq
    exact hne (by rw [← φ.right_inv h13, ← φ.right_inv h23, this])
  subst he1
  have hd : HasDerivAt (fun z ↦ b65g_sFun D t a b (φ.symm z)) (l z₀) z₀ := by
    have h := hκd.const_add (b65g_sFun D t a b x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hfl] with z hz
    rw [hz, pow_one]
  rw [hd.deriv]
  exact hl0

end Fibre

end HodgeLean.Foundations.Program
