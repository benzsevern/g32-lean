import HodgeLean.Foundations.Program.CoverAnalytic
import HodgeLean.Foundations.Program.CurveJacobianDefs
import HodgeLean.Foundations.Program.KernelFramesFamilyNormal

/-! # Complex-analytic foundations for the cover dictionary, stage 2 (proofs)

One auxiliary per statement of `CoverAnalyticTwo.lean`, with its helpers. Statements 1–4 and 6–8
use Mathlib and `b3_HolForm` only; statement 5 uses the 5c record and the 5d flow results.
Statement 3 extends the chart coefficient by Riemann's removable singularity theorem; statement 6
derives Liouville's formula for `ContinuousLinearMap.det` from `Matrix.det_one_add_smul`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem caf_eq_mul_const_of_ode_aux [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (hc : IsPreconnected U) (A Y Z : ℂ → E →L[ℂ] E)
    (hY : ∀ z ∈ U, HasDerivAt Y (A z * Y z) z) (hZ : ∀ z ∈ U, HasDerivAt Z (A z * Z z) z)
    (hZu : ∀ z ∈ U, IsUnit (Z z)) :
    ∃ K : E →L[ℂ] E, ∀ z ∈ U, Y z = Z z * K := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set W : ℂ → E →L[ℂ] E := fun z ↦ Ring.inverse (Z z) * Y z with hW
  have hWd : ∀ z ∈ U, HasDerivAt W 0 z := by
    intro z hz
    obtain ⟨u, hu⟩ := hZu z hz
    have hinv : HasDerivAt (fun w ↦ Ring.inverse (Z w))
        (-(↑u⁻¹ * (A z * Z z) * ↑u⁻¹)) z := by
      have h0 := hasFDerivAt_ringInverse (𝕜 := ℂ) u
      rw [hu] at h0
      convert h0.comp_hasDerivAt z (hZ z hz) using 1
      · rfl
      · rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    have h := hinv.mul (hY z hz)
    convert h using 1
    rw [← hu, Ring.inverse_unit]
    simp only [mul_assoc, Units.mul_inv_cancel_left, neg_mul, neg_add_cancel]
  rcases U.eq_empty_or_nonempty with rfl | ⟨z₁, hz₁⟩
  · exact ⟨0, fun z hz ↦ hz.elim⟩
  refine ⟨W z₁, fun z hz ↦ ?_⟩
  have hconst := hU.is_const_of_deriv_eq_zero hc
    (fun w hw ↦ (hWd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hWd w hw).deriv) hz hz₁
  rw [← hconst, hW]
  obtain ⟨u, hu⟩ := hZu z hz
  simp only [← hu, Ring.inverse_unit, ← mul_assoc, Units.mul_inv, one_mul]

/-- In a space charted on `ℂ`, every point is a limit of other points. -/
theorem caf_nhdsNE_neBot {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] (x : M) :
    (𝓝[≠] x).NeBot := by
  set e := chartAt ℂ x
  have hx := mem_chart_source ℂ x
  have hT : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (e.continuousAt_symm (e.map_source hx)).tendsto
      rw [e.left_inv hx] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds (e.map_source hx)),
        self_mem_nhdsWithin] with z hz hzx
      intro h
      apply hzx
      rw [← e.right_inv hz, show e.symm z = x from h]
      rfl
  exact hT.neBot

theorem caf_holForm_ext_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (θ θ' : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : θ ∈ b3_HolForm ℂ C) (hθ' : θ' ∈ b3_HolForm ℂ C) (F : Set C) (hF : F.Finite)
    (h : ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F → θ u = θ' u) : θ = θ' := by
  have : ∀ x : C, (𝓝[≠] x).NeBot := caf_nhdsNE_neBot
  have hd : Dense (Fᶜ) := by
    have := dense_univ.sdiff_finite hF
    rwa [← compl_eq_univ_sdiff] at this
  have hd' : Dense ((Bundle.TotalSpace.proj : TangentBundle 𝓘(ℂ, ℂ) C → C) ⁻¹' Fᶜ) :=
    hd.preimage (FiberBundle.isOpenMap_proj ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := C)))
  exact Continuous.ext_on hd' hθ.1.continuous hθ'.1.continuous fun u hu ↦ h u hu

section ChartForms

variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]

/-- The chart differential `u ↦ dφ(u)` of the chart at `x` is holomorphic on the tangent bundle
over the chart domain. -/
theorem caf_contMDiffAt_chart_differential (x : C) (u : TangentBundle 𝓘(ℂ, ℂ) C)
    (hu : u.1 ∈ (chartAt ℂ x).source) :
    ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω
      (fun u : TangentBundle 𝓘(ℂ, ℂ) C ↦ mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) u.1 u.2)
      u := by
  set s := (chartAt ℂ x).source
  have hs : IsOpen s := (chartAt ℂ x).open_source
  have hT := (contMDiffOn_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := x)).contMDiffOn_tangentMapWithin
    (m := ω) (by simp) hs.uniqueMDiffOn
  have hU : Bundle.TotalSpace.proj ⁻¹' s ∈ 𝓝 u :=
    (hs.preimage (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := C)))).mem_nhds hu
  have h1 := ((contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ, ℂ)).contMDiffAt).comp u
    (hT.contMDiffAt hU)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hU] with p hp
  change _ = (mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) s p.1) p.2
  rw [mfderivWithin_of_isOpen hs hp]

/-- The chart vector field `z ↦ ∂/∂z` at `φ.symm z` is holomorphic on the chart target. -/
theorem caf_contMDiffAt_chart_field (x : C) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent ω
      (fun z : ℂ ↦ (⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ :
          TangentBundle 𝓘(ℂ, ℂ) C)) z := by
  set t := (extChartAt 𝓘(ℂ, ℂ) x).target
  have ht : IsOpen t := isOpen_extChartAt_target x
  have hT := (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) (n := ω) x).contMDiffOn_tangentMapWithin
    (m := ω) (by simp) ht.uniqueMDiffOn
  have hV : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent ω
      (fun z : ℂ ↦ (⟨z, (1 : ℂ)⟩ : TangentBundle 𝓘(ℂ, ℂ) ℂ)) z := by
    have := (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (n := ω) (s := univ) (x := z)
      (V := fun _ ↦ (1 : ℂ))).2 (contDiffWithinAt_const (𝕜 := ℂ) (c := (1 : ℂ)))
    exact contMDiffWithinAt_univ.1 this
  have hU : Bundle.TotalSpace.proj ⁻¹' t ∈ 𝓝 (⟨z, (1 : ℂ)⟩ : TangentBundle 𝓘(ℂ, ℂ) ℂ) :=
    (ht.preimage (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := ℂ)))).mem_nhds hz
  have h1 := (hT.contMDiffAt hU).comp z hV
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [ht.mem_nhds hz] with w hw
  change _ = (⟨_, mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm t w (1 : ℂ)⟩ :
    TangentBundle 𝓘(ℂ, ℂ) C)
  rw [mfderivWithin_of_isOpen ht hw]

omit [IsManifold 𝓘(ℂ, ℂ) ω C] in
/-- A fibrewise linear function on the tangent space at `φ.symm z`, on the image of the chart
derivative. -/
theorem caf_linear_chart (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (x : C) (z : ℂ)
    (hlin : ∀ (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)),
      θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, a • v + w⟩ =
        a * θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, v⟩ + θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, w⟩)
    (a : ℂ) :
    θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z a⟩ =
      a * θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ := by
  set L := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z
  have hL : L a = a • L (1 : ℂ) + 0 := by
    rw [add_zero]
    exact (show L a = L (a • (1 : ℂ)) by rw [smul_eq_mul, mul_one]).trans (L.map_smul a (1 : ℂ))
  have h0 : θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, 0⟩ = 0 := by
    have := hlin 1 0 0
    simp only [smul_zero, add_zero, one_mul] at this
    linear_combination -this
  rw [hL, hlin, h0, add_zero]

/-- The chart derivative of the inverse chart inverts the chart derivative. -/
theorem caf_mfderiv_chart_symm (x : C) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target)
    (v : TangentSpace 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) ((extChartAt 𝓘(ℂ, ℂ) x).symm z) v) = v := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℂ, ℂ)) (x := x) hz
  rw [show range (𝓘(ℂ, ℂ) : ℂ → ℂ) = univ by simp, mfderivWithin_univ] at hcomp
  exact congrArg (fun L ↦ L v) hcomp

/-- A fibrewise linear function at a point of the chart domain is its value on `∂/∂z` times the
chart differential. -/
theorem caf_linear_chart_at (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (x y : C)
    (hy : y ∈ (chartAt ℂ x).source)
    (hlin : ∀ (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) y),
      θ ⟨y, a • v + w⟩ = a * θ ⟨y, v⟩ + θ ⟨y, w⟩)
    (v : TangentSpace 𝓘(ℂ, ℂ) y) (a : ℂ)
    (ha : a = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y v) :
    θ ⟨y, v⟩ = a * θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm (extChartAt 𝓘(ℂ, ℂ) x y),
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm (extChartAt 𝓘(ℂ, ℂ) x y) (1 : ℂ)⟩ := by
  set z := extChartAt 𝓘(ℂ, ℂ) x y
  have hys : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source := by rwa [extChartAt_source]
  have hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := (extChartAt 𝓘(ℂ, ℂ) x).map_source hys
  have hy' : (extChartAt 𝓘(ℂ, ℂ) x).symm z = y := (extChartAt 𝓘(ℂ, ℂ) x).left_inv hys
  have hlin' : ∀ (b : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)),
      θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, b • v + w⟩ =
        b * θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, v⟩ + θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, w⟩ := by
    rw [hy']; exact hlin
  have key := caf_linear_chart θ x z hlin' a
  have hinv := caf_mfderiv_chart_symm x z hz v
  have ha' : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x)
      ((extChartAt 𝓘(ℂ, ℂ) x).symm z) v = a := by
    rw [hy']; exact ha.symm
  rw [ha'] at hinv
  rw [hinv] at key
  calc θ ⟨y, v⟩ = θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, v⟩ := by rw [hy']
    _ = _ := key

/-- Riemann's removable singularity theorem for the chart coefficient of a form. -/
theorem caf_chart_coeff_extend [T2Space C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (F : Set C) (hF : F.Finite)
    (hhol : ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F →
      ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω θ u)
    (x : C) (B : ℝ) (hB : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x), g z = θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ := by
  set φ := extChartAt 𝓘(ℂ, ℂ) x
  set a := φ x
  set c : ℂ → ℂ := fun z ↦ θ ⟨φ.symm z, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ.symm z (1 : ℂ)⟩
  have htarget : φ.target ∈ 𝓝 a := (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hFx : (F \ {x})ᶜ ∈ 𝓝 x :=
    (hF.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hsymm : ∀ᶠ z in 𝓝 a, φ.symm z ∈ (F \ {x})ᶜ := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x).tendsto
    rw [extChartAt_to_inv] at this
    exact this hFx
  have hgood : ∀ᶠ z in 𝓝[≠] a, z ∈ φ.target ∧ φ.symm z ∉ F := by
    filter_upwards [nhdsWithin_le_nhds htarget, nhdsWithin_le_nhds hsymm, self_mem_nhdsWithin]
      with z hz h1 h2
    refine ⟨hz, fun hF' ↦ h1 ⟨hF', fun hzx ↦ h2 ?_⟩⟩
    rw [← φ.right_inv hz, show φ.symm z = x from hzx]
    rfl
  have hdiff : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ c z := by
    filter_upwards [hgood] with z ⟨hz, hzF⟩
    have h1 := (hhol _ hzF).comp z (caf_contMDiffAt_chart_field x z hz)
    exact mdifferentiableAt_iff_differentiableAt.1 (h1.mdifferentiableAt (by simp))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_nhdsWithin_iff.1 (hdiff.and hB))
  have hd : DifferentiableOn ℂ c (ball a r \ {a}) :=
    fun z hz ↦ (hball z hz.1 hz.2).1.differentiableWithinAt
  have hb : BddAbove (norm ∘ c '' (ball a r \ {a})) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hball z hz.1 hz.2).2
  have hext := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds a hr) hd hb
  refine ⟨_, hext.analyticAt (ball_mem_nhds a hr), ?_⟩
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin] with z _ hz
  exact Function.update_of_ne hz _ _

end ChartForms

theorem caf_holForm_extend_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (F : Set C) (hF : F.Finite)
    (hhol : ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F →
      ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω θ u)
    (hlin : ∀ x ∉ F, ∀ (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩)
    (hbdd : ∀ x ∈ F, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) :
    ∃ θ' ∈ b3_HolForm ℂ C, ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F → θ' u = θ u := by
  classical
  have hext : ∀ x ∈ F, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x), g z = θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ := fun x hx ↦
    let ⟨B, hB⟩ := hbdd x hx
    caf_chart_coeff_extend θ F hF hhol x B hB
  let G : C → ℂ → ℂ := fun x ↦ if hx : x ∈ F then (hext x hx).choose else 0
  have hG : ∀ x (hx : x ∈ F), AnalyticAt ℂ (G x) (extChartAt 𝓘(ℂ, ℂ) x x) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x), G x z = θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ := by
    intro x hx
    simp only [G, hx, ↓reduceDIte]
    exact (hext x hx).choose_spec
  let D : C → TangentBundle 𝓘(ℂ, ℂ) C → ℂ := fun x u ↦
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) u.1 u.2
  let θ' : TangentBundle 𝓘(ℂ, ℂ) C → ℂ := fun u ↦
    if u.1 ∈ F then G u.1 (extChartAt 𝓘(ℂ, ℂ) u.1 u.1) * D u.1 u else θ u
  have hopen : IsOpen ((Bundle.TotalSpace.proj : TangentBundle 𝓘(ℂ, ℂ) C → C) ⁻¹' Fᶜ) :=
    hF.isClosed.isOpen_compl.preimage (FiberBundle.continuous_proj ℂ _)
  refine ⟨θ', ⟨?_, ?_⟩, fun u hu ↦ by simp only [θ', hu, ↓reduceIte]⟩
  · intro u
    obtain ⟨x, v₀⟩ := u
    by_cases hx : x ∈ F
    · set φ := extChartAt 𝓘(ℂ, ℂ) x
      set Ψ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ := fun u ↦ G x (φ u.1) * D x u
      have hsm : ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω Ψ ⟨x, v₀⟩ := by
        have hφ : ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω
            (fun u : TangentBundle 𝓘(ℂ, ℂ) C ↦ φ u.1) ⟨x, v₀⟩ :=
          (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (x := x)).comp _
            (Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))).contMDiffAt
        have hGc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (G x) (φ x) :=
          (hG x hx).1.contDiffAt.contMDiffAt
        have := (hGc.comp (⟨x, v₀⟩ : TangentBundle 𝓘(ℂ, ℂ) C) hφ).mul
          (caf_contMDiffAt_chart_differential x ⟨x, v₀⟩ (mem_chart_source ℂ x))
        exact this
      refine hsm.congr_of_eventuallyEq ?_
      have hsrc : (chartAt ℂ x).source ∈ 𝓝 x :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      have hFx : (F \ {x})ᶜ ∈ 𝓝 x :=
        (hF.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      have hcoef : ∀ᶠ y in 𝓝 x, φ y ≠ φ x → G x (φ y) = θ ⟨φ.symm (φ y),
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ.symm (φ y) (1 : ℂ)⟩ :=
        (continuousAt_extChartAt x).tendsto.eventually
          (eventually_nhdsWithin_iff.1 (hG x hx).2)
      have hev : ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ x).source ∧ y ∉ F \ {x} ∧
          (φ y ≠ φ x → G x (φ y) = θ ⟨φ.symm (φ y),
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ.symm (φ y) (1 : ℂ)⟩) := by
        filter_upwards [hsrc, hFx, hcoef] with y h1 h2 h3
        exact ⟨h1, h2, h3⟩
      have hev' := (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := C))).continuousAt
        (x := (⟨x, v₀⟩ : TangentBundle 𝓘(ℂ, ℂ) C)) |>.tendsto.eventually hev
      filter_upwards [hev'] with u ⟨h1, h2, h3⟩
      obtain ⟨y, v⟩ := u
      by_cases hyx : y = x
      · subst hyx
        simp only [θ', Ψ, hx, ↓reduceIte]
        rfl
      · have hyF : y ∉ F := fun h ↦ h2 ⟨h, hyx⟩
        have hne : φ y ≠ φ x := fun h ↦ hyx
          ((extChartAt 𝓘(ℂ, ℂ) x).injOn (by rwa [extChartAt_source])
            (by rw [extChartAt_source]; exact mem_chart_source ℂ x) h)
        simp only [θ', Ψ, hyF, ↓reduceIte]
        rw [h3 hne, mul_comm]
        exact caf_linear_chart_at θ x y h1 (hlin y hyF) v (D x ⟨y, v⟩) rfl
    · refine (hhol _ hx).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx] with u hu
      simp only [θ', show u.1 ∉ F from hu, ↓reduceIte]
  · intro y a v w
    by_cases hy : y ∈ F
    · have hD : D y ⟨y, a • v + w⟩ = a * D y ⟨y, v⟩ + D y ⟨y, w⟩ := by
        simp only [D]
        rw [map_add, map_smul]
        rfl
      simp only [θ', hy, ↓reduceIte]
      rw [hD]
      ring
    · simp only [θ', hy, ↓reduceIte]
      exact hlin y hy a v w

/-- A punctured disc in `ℂ` is preconnected. -/
theorem caf_isPreconnected_ball_diff (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball c r \ {c}) := by
  set φ := OpenPartialHomeomorph.univBall c r
  have himg : φ '' ({0}ᶜ) = ball c r \ {c} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target c hr]
        exact φ.map_source (by simp [φ, OpenPartialHomeomorph.univBall_source])
      · intro h
        apply hz
        have := φ.left_inv (x := z) (by simp [φ, OpenPartialHomeomorph.univBall_source])
        rw [show φ z = c from h] at this
        rw [← this]
        exact OpenPartialHomeomorph.univBall_symm_apply_center c r
    · rintro ⟨hw, hwc⟩
      have hwt : w ∈ φ.target := by rwa [OpenPartialHomeomorph.univBall_target c hr]
      refine ⟨φ.symm w, ?_, φ.right_inv hwt⟩
      intro h0
      apply hwc
      rw [← φ.right_inv hwt, show φ.symm w = 0 from h0]
      exact OpenPartialHomeomorph.univBall_apply_zero c r
  rw [← himg]
  exact (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected.image _
    (φ.continuousOn.mono fun z _ ↦ by simp [φ, OpenPartialHomeomorph.univBall_source])

/-- Removing a point from an open preconnected subset of a space charted on `ℂ` keeps it
preconnected. -/
theorem caf_isPreconnected_diff_singleton {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [T2Space M] {W : Set M} (hW : IsOpen W) (hc : IsPreconnected W) (s : M) :
    IsPreconnected (W \ {s}) := by
  by_cases hs : s ∉ W
  · rwa [sdiff_singleton_eq_self hs]
  push Not at hs
  set e := chartAt ℂ s
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  have hsT : e s ∈ e.target ∩ e.symm ⁻¹' W :=
    ⟨e.map_source (mem_chart_source ℂ s), by
      simp only [mem_preimage, e.left_inv (mem_chart_source ℂ s)]; exact hs⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hT _ hsT
  set N := e.source ∩ e ⁻¹' ball (e s) r
  have hNo : IsOpen N := e.isOpen_inter_preimage isOpen_ball
  have hsN : s ∈ N := ⟨mem_chart_source ℂ s, mem_ball_self hr⟩
  have hNW : N ⊆ W := fun y hy ↦ by
    have := (hball hy.2).2
    rwa [mem_preimage, e.left_inv hy.1] at this
  have hA : N \ {s} = e.symm '' (ball (e s) r \ {e s}) := by
    ext y
    constructor
    · rintro ⟨hy, hys⟩
      refine ⟨e y, ⟨hy.2, fun h ↦ hys ?_⟩, e.left_inv hy.1⟩
      exact e.injOn hy.1 (mem_chart_source ℂ s) h
    · rintro ⟨z, ⟨hz, hzs⟩, rfl⟩
      have hzt : z ∈ e.target := (hball hz).1
      refine ⟨⟨e.map_target hzt, ?_⟩, fun h ↦ hzs ?_⟩
      · rw [mem_preimage, e.right_inv hzt]; exact hz
      · rw [← e.right_inv hzt, show e.symm z = s from h]
        rfl
  have hApc : IsPreconnected (N \ {s}) := by
    rw [hA]
    exact (caf_isPreconnected_ball_diff _ hr).image _
      (e.continuousOn_symm.mono fun z hz ↦ (hball hz.1).1)
  -- the main argument, with the punctured chart disc inside `u`
  have key : ∀ u v : Set M, IsOpen u → IsOpen v → W \ {s} ⊆ u ∪ v →
      W \ {s} ∩ (u ∩ v) = ∅ → N \ {s} ⊆ u → W \ {s} ⊆ u ∨ W \ {s} ⊆ v := by
    intro u v hu hv hcov hdis hNu
    have hv' : IsOpen (v \ {s}) := hv.sdiff isClosed_singleton
    have hcov' : W ⊆ (u ∪ N) ∪ (v \ {s}) := by
      intro w hw
      by_cases hws : w = s
      · exact Or.inl (Or.inr (hws ▸ hsN))
      · rcases hcov ⟨hw, hws⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hws⟩
    have hdis' : W ∩ ((u ∪ N) ∩ (v \ {s})) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro w ⟨hw, huN, hwv, hws⟩
      have hwu : w ∈ u := huN.elim id fun h ↦ hNu ⟨h, hws⟩
      have : w ∈ W \ {s} ∩ (u ∩ v) := ⟨⟨hw, hws⟩, hwu, hwv⟩
      rw [hdis] at this
      exact this
    rcases isPreconnected_iff_subset_of_disjoint.1 hc _ _ (hu.union hNo) hv' hcov' hdis' with
      h | h
    · left
      intro w hw
      exact (h hw.1).elim id fun h' ↦ hNu ⟨h', hw.2⟩
    · right
      exact fun w hw ↦ (h hw.1).1
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdis
  have hAsub : N \ {s} ⊆ W \ {s} := sdiff_subset_sdiff_left hNW
  rcases isPreconnected_iff_subset_of_disjoint.1 hApc u v hu hv (hAsub.trans hcov) (by
    rw [eq_empty_iff_forall_notMem]
    intro w hw
    have : w ∈ W \ {s} ∩ (u ∩ v) := ⟨hAsub hw.1, hw.2⟩
    rw [hdis] at this
    exact this) with h | h
  · exact key u v hu hv hcov hdis h
  · refine (key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v]) h).symm

theorem caf_isPathConnected_compl_finite_aux (M : Type) [TopologicalSpace M]
    [ChartedSpace ℂ M] [T2Space M] [ConnectedSpace M] (S : Set M) (hS : S.Finite) :
    IsPathConnected Sᶜ := by
  have : ∀ x : M, (𝓝[≠] x).NeBot := caf_nhdsNE_neBot
  have hpre : IsPreconnected Sᶜ := by
    induction S, hS using Set.Finite.induction_on with
    | empty => simpa using isPreconnected_univ
    | @insert a T _ hT ih =>
      rw [← union_singleton, compl_union, ← sdiff_eq]
      exact caf_isPreconnected_diff_singleton hT.isClosed.isOpen_compl ih a
  have hne : Sᶜ.Nonempty := by
    have hd : Dense (univ \ S) := dense_univ.sdiff_finite hS
    rw [← compl_eq_univ_sdiff] at hd
    exact hd.nonempty
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ℂ M
  exact (hS.isClosed.isOpen_compl.isConnected_iff_isPathConnected).1 ⟨hne, hpre⟩

/-- A `4 × 4` matrix with `A² = c A`, `trace A = c ≠ 0` is conjugate to `diag(0, 0, 0, c)`. -/
theorem caf_diag_of_sq (A : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (hc : c ≠ 0)
    (hsq : A * A = c • A) (htr : Matrix.trace A = c) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℂ, IsUnit P ∧ A * P = P * diagonal ![0, 0, 0, c] := by
  set f : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) := Matrix.toLin' A
  set e : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) := c⁻¹ • f
  have hff : f * f = c • f := by
    simp only [f]
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hsq, map_smul]
  have he : IsIdempotentElem e := by
    simp only [IsIdempotentElem, e, smul_mul_smul_comm, hff, smul_smul]
    rw [show c⁻¹ * c⁻¹ * c = c⁻¹ by field_simp]
  have htre : LinearMap.trace ℂ _ e = 1 := by
    simp only [e, map_smul, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 4)),
      f, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hc]
  have hR : Module.finrank ℂ (LinearMap.range e) = 1 := by
    have := (LinearMap.IsIdempotentElem.isProj_range e he).trace
    rw [htre] at this
    exact_mod_cast this.symm
  have hcompl : IsCompl (LinearMap.ker e) (LinearMap.range e) := (LinearMap.IsIdempotentElem.isCompl he).symm
  have hK : Module.finrank ℂ (LinearMap.ker e) = 3 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hR, Module.finrank_fin_fun] at this
    omega
  let bK : Module.Basis (Fin 3) ℂ (LinearMap.ker e) := Module.finBasisOfFinrankEq _ _ hK
  let bR : Module.Basis (Fin 1) ℂ (LinearMap.range e) := Module.finBasisOfFinrankEq _ _ hR
  let b : Module.Basis (Fin 3 ⊕ Fin 1) ℂ (Fin 4 → ℂ) :=
    (bK.prod bR).map (Submodule.prodEquivOfIsCompl _ _ hcompl)
  let d : Fin 3 ⊕ Fin 1 → ℂ := Sum.elim (fun _ ↦ 0) (fun _ ↦ c)
  have hb : ∀ s, f (b s) = d s • b s := by
    rintro (k | k)
    · have hmem : b (Sum.inl k) ∈ LinearMap.ker e := by
        simp [b, Submodule.coe_prodEquivOfIsCompl']
      have : e (b (Sum.inl k)) = 0 := hmem
      simp only [e, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hc, false_or] at this
      simp [d, this]
    · have hmem : b (Sum.inr k) ∈ LinearMap.range e := by
        simp [b, Submodule.coe_prodEquivOfIsCompl']
      have : e (b (Sum.inr k)) = b (Sum.inr k) := (LinearMap.IsIdempotentElem.isProj_range e he).map_id _ hmem
      simp only [e, LinearMap.smul_apply] at this
      simp only [d, Sum.elim_inr]
      calc f (b (Sum.inr k)) = c • (c⁻¹ • f (b (Sum.inr k))) := by
            rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • b (Sum.inr k) := by rw [this]
  let bb : Module.Basis (Fin 4) ℂ (Fin 4 → ℂ) := b.reindex finSumFinEquiv
  have hd : ∀ j : Fin 4, ![0, 0, 0, c] j = d (finSumFinEquiv.symm j) := by
    intro j; fin_cases j <;> rfl
  refine ⟨(Pi.basisFun ℂ (Fin 4)).toMatrix bb, ?_, ?_⟩
  · have := (Pi.basisFun ℂ (Fin 4)).invertibleToMatrix bb
    exact isUnit_of_invertible _
  · ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    have h1 := congrFun (hb (finSumFinEquiv.symm j)) i
    simp only [f, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] at h1
    simp only [bb, Module.Basis.reindex_apply, hd]
    rw [h1, mul_comm]

/-- Non-resonance of `ad a` when `a² = c a`: `k T = a T − T a` forces `T = 0` unless
`k ∈ {0, c, −c}`. -/
theorem caf_ad_injective {R : Type*} [Ring R] [Algebra ℂ R] (a T : R) (c k : ℂ)
    (hsq : a * a = c • a) (hk0 : k ≠ 0) (hk1 : k ≠ c) (hk2 : k ≠ -c)
    (h : k • T = a * T - T * a) : T = 0 := by
  have h1 : (k - c) • (a * T) = -(a * T * a) := by
    have := congrArg (a * ·) h
    simp only [mul_smul_comm, mul_sub, ← mul_assoc, hsq, smul_mul_assoc] at this
    rw [sub_smul, this]; abel
  have h2 : (k + c) • (T * a) = a * T * a := by
    have := congrArg (· * a) h
    simp only [smul_mul_assoc, sub_mul, mul_assoc, hsq, mul_smul_comm] at this
    rw [add_smul, this, ← mul_assoc]; abel
  have h3 : k • (a * T * a) = 0 := by
    have := congrArg (fun X ↦ a * X * a) h
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul] at this
    rw [this, ← mul_assoc, hsq, mul_assoc, mul_assoc, mul_assoc, hsq]
    simp only [smul_mul_assoc, mul_smul_comm, sub_self]
  have haTa : a * T * a = 0 := (smul_eq_zero.1 h3).resolve_left hk0
  have haT : a * T = 0 := by
    rw [haTa, neg_zero] at h1
    exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hk1)
  have hTa : T * a = 0 := by
    rw [haTa] at h2
    exact (smul_eq_zero.1 h2).resolve_left (by
      intro h0; exact hk2 (eq_neg_of_add_eq_zero_left h0))
  rw [haT, hTa, sub_zero] at h
  exact (smul_eq_zero.1 h).resolve_left hk0

theorem caf_moving_spectrum_aux {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    ∃ q : ℚ, (q = 1 / 3 ∨ q = 2 / 3) ∧ ∀ θ ∈ ball (0 : ℂ) O.radius,
      Matrix.trace (b65q_res O.residue θ (Sum.inr x)) = (q : ℂ) ∧
      (∃ P : Matrix (Fin 4) (Fin 4) ℂ, IsUnit P ∧
        b65q_res O.residue θ (Sum.inr x) * P = P * diagonal ![0, 0, 0, (q : ℂ)]) ∧
      ∀ k : ℕ, 0 < k → Function.Bijective
        (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦
          (k : ℂ) • T - (O.residue θ (Sum.inr x) * T - T * O.residue θ (Sum.inr x))) := by
  have hvals : ∀ e : Fin 2, Matrix.trace (b65q_BQ e) = 1 / 3 ∨ Matrix.trace (b65q_BQ e) = 2 / 3 := by
    intro e
    fin_cases e
    · left; decide +kernel
    · right; decide +kernel
  set q : ℚ := Matrix.trace (b65q_BQ (b65q_fibreIndex x)) with hqdef
  have hq : q = 1 / 3 ∨ q = 2 / 3 := hvals _
  refine ⟨q, hq, fun θ hθ ↦ ?_⟩
  have htr : Matrix.trace (b65q_res O.residue θ (Sum.inr x)) = (q : ℂ) := by
    rw [b65q_trace_flow O _ θ hθ, b65q_trace_zero_inr]
  have hsq := b65q_rank_one_flow O x θ hθ
  rw [b65q_trace_zero_inr] at hsq
  have hc : (q : ℂ) ≠ 0 := by exact_mod_cast b65q_BQ_trace_ne _
  refine ⟨htr, caf_diag_of_sq _ _ hc hsq htr, fun k hk ↦ ?_⟩
  set R := O.residue θ (Sum.inr x)
  have hR : R * R = (q : ℂ) • R := by
    apply b65q_mat_injective
    change b65q_matAlg (R * R) = b65q_matAlg ((q : ℂ) • R)
    rw [map_mul, map_smul]
    exact hsq
  have hk1 : (k : ℂ) ≠ (q : ℂ) := by
    intro h
    have : (k : ℚ) = q := by exact_mod_cast h
    have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    rcases hq with hq | hq <;> rw [hq] at this <;> linarith
  have hk2 : (k : ℂ) ≠ -(q : ℂ) := by
    intro h
    have : (k : ℚ) = -q := by exact_mod_cast h
    have hk' : (0 : ℚ) ≤ k := by positivity
    rcases hq with hq | hq <;> rw [hq] at this <;> linarith
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  let Φ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) →ₗ[ℂ] ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) :=
    (k : ℂ) • LinearMap.id - (LinearMap.mulLeft ℂ R - LinearMap.mulRight ℂ R)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine caf_ad_injective R T q k hR hk0 hk1 hk2 ?_
    have : (k : ℂ) • T - (R * T - T * R) = 0 := hT
    exact sub_eq_zero.1 this
  exact ⟨hΦ, LinearMap.injective_iff_surjective.1 hΦ⟩

/-- A continuous linear functional of a meromorphic germ is meromorphic. -/
theorem caf_meromorphicAt_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) {f : ℂ → F} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    MeromorphicAt (fun z ↦ L (f z)) z₀ := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have := (L.analyticAt _).comp hn
  simp only [Function.comp_def, map_smul] at this
  exact this

theorem caf_analyticAt_clm {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) {f : X → F} {z₀ : X} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (fun z ↦ L (f z)) z₀ :=
  (L.analyticAt _).comp hf

/-- The determinant of an operator through the matrix entries in the standard basis. -/
theorem caf_det_eq_matrix [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    T.det = Matrix.det (Matrix.of fun i j ↦
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ E).coord i)).comp
        (ContinuousLinearMap.apply ℂ E (Module.finBasis ℂ E j)) T) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.finBasis ℂ E)]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply]

theorem caf_analyticAt_det [FiniteDimensional ℂ E] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {H : X → E →L[ℂ] E} {z₀ : X}
    (hH : AnalyticAt ℂ H z₀) : AnalyticAt ℂ (fun z ↦ (H z).det) z₀ := by
  simp only [caf_det_eq_matrix, Matrix.det_apply', Matrix.of_apply]
  exact Finset.analyticAt_fun_sum _ fun σ _ ↦ analyticAt_const.fun_mul
    (Finset.analyticAt_fun_prod _ fun i _ ↦ caf_analyticAt_clm _ hH)

theorem caf_meromorphicAt_det [FiniteDimensional ℂ E] {Y : ℂ → E →L[ℂ] E} {z₀ : ℂ}
    (hY : MeromorphicAt Y z₀) : MeromorphicAt (fun z ↦ (Y z).det) z₀ := by
  simp only [caf_det_eq_matrix, Matrix.det_apply', Matrix.of_apply]
  refine MeromorphicAt.fun_sum fun σ _ ↦ (analyticAt_const (𝕜 := ℂ)).meromorphicAt.mul ?_
  exact MeromorphicAt.fun_prod fun i _ ↦ caf_meromorphicAt_clm _ hY

theorem caf_isUnit_of_det_ne_zero [FiniteDimensional ℂ E] (T : E →L[ℂ] E) (h : T.det ≠ 0) :
    IsUnit T := by
  have hl : IsUnit (T : E →ₗ[ℂ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  let e : E ≃ₗ[ℂ] E := LinearEquiv.ofBijective _ ((Module.End.isUnit_iff _).1 hl)
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℂ E).symm e.toContinuousLinearEquiv, ?_⟩
  ext v
  rfl

/-- `t ↦ det (1 + t N)` has derivative `trace N` at `0`. -/
theorem caf_hasDerivAt_det_one_add [FiniteDimensional ℂ E] (N : E →L[ℂ] E) :
    HasDerivAt (fun t : ℂ ↦ (1 + t • N).det) (LinearMap.trace ℂ E (N : E →ₗ[ℂ] E)) 0 := by
  set b := Module.finBasis ℂ E
  set Nm := LinearMap.toMatrix b b (N : E →ₗ[ℂ] E)
  set q := (1 + (Polynomial.X : Polynomial ℂ) • Nm.map Polynomial.C).det.divX.divX
  have hfun : (fun t : ℂ ↦ (1 + t • N).det) =
      fun t ↦ 1 + Nm.trace * t + q.eval t * t ^ 2 := by
    funext t
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ← Matrix.det_one_add_smul]
    congr 1
    rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
      ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix_one]
  rw [hfun, LinearMap.trace_eq_matrix_trace ℂ b]
  have h1 : HasDerivAt (fun t : ℂ ↦ 1 + Nm.trace * t) Nm.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul Nm.trace).const_add 1
  have h2 : HasDerivAt (fun t : ℂ ↦ q.eval t * t ^ 2) 0 0 := by
    have := (q.hasDerivAt 0).fun_mul ((hasDerivAt_pow 2 (0 : ℂ)))
    simpa using this
  simpa using h1.fun_add h2

/-- **Liouville's formula** at an invertible value: if `Y' = B Y` at `z` and `Y z` is a unit,
then `(det Y)' = trace B · det Y` at `z`. -/
theorem caf_hasDerivAt_det [FiniteDimensional ℂ E] {Y : ℂ → E →L[ℂ] E} {B : E →L[ℂ] E}
    {z : ℂ} (hY : HasDerivAt Y (B * Y z) z) (hu : IsUnit (Y z)) :
    HasDerivAt (fun w ↦ (Y w).det)
      (LinearMap.trace ℂ E (B : E →ₗ[ℂ] E) * (Y z).det) z := by
  obtain ⟨u, hu⟩ := hu
  set M : ℂ → E →L[ℂ] E := fun w ↦ ↑u⁻¹ * Y w
  have hM : HasDerivAt M (↑u⁻¹ * (B * Y z)) z := by
    simpa [M] using hY.const_mul (↑u⁻¹ : E →L[ℂ] E)
  have hMz : M z = 1 := by simp [M, ← hu]
  -- the determinant is differentiable at `1`
  have hdiff : DifferentiableAt ℂ (fun T : E →L[ℂ] E ↦ T.det) 1 :=
    (caf_analyticAt_det (H := fun T : E →L[ℂ] E ↦ T) analyticAt_id).differentiableAt
  have hfd : ∀ N : E →L[ℂ] E, fderiv ℂ (fun T : E →L[ℂ] E ↦ T.det) 1 N =
      LinearMap.trace ℂ E (N : E →ₗ[ℂ] E) := by
    intro N
    have hline : HasDerivAt (fun t : ℂ ↦ 1 + t • N) N 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const N).const_add 1
    have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℂ)) hline (by simp)
    exact h1.unique (caf_hasDerivAt_det_one_add N)
  have hdM : HasDerivAt (fun w ↦ (M w).det)
      (LinearMap.trace ℂ E (B : E →ₗ[ℂ] E)) z := by
    have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq z hM hMz.symm
    refine h1.congr_deriv ?_
    rw [hfd, ← hu, ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
      ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc, ← ContinuousLinearMap.toLinearMap_mul,
      Units.mul_inv, ContinuousLinearMap.toLinearMap_one, one_mul]
  have hY' : (fun w ↦ (Y w).det) = fun w ↦ (↑u : E →L[ℂ] E).det * (M w).det := by
    funext w
    simp only [M, ContinuousLinearMap.det]
    rw [← LinearMap.det_comp]
    congr 1
    ext v
    change _ = ((↑u : E →L[ℂ] E) * ↑u⁻¹) (Y w v)
    rw [Units.mul_inv]
    rfl
  rw [hY']
  convert hdM.const_mul (↑u : E →L[ℂ] E).det using 1
  rw [← hu, mul_comm]

theorem caf_det_order_aux [FiniteDimensional ℂ E] (Y : ℂ → E →L[ℂ] E) (z₀ : ℂ)
    (A₀ : E →L[ℂ] E) (G : ℂ → E →L[ℂ] E) (hY : MeromorphicAt Y z₀) (hG : ContinuousAt G z₀)
    (hunit : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (Y z))
    (hode : ∀ᶠ z in 𝓝[≠] z₀,
      HasDerivAt Y (((z - z₀)⁻¹ • (A₀ + (z - z₀) • G z)) * Y z) z) :
    ∃ n : ℤ, meromorphicOrderAt (fun z ↦ (Y z).det) z₀ = (n : WithTop ℤ) ∧
      (n : ℂ) = LinearMap.trace ℂ E (A₀ : E →ₗ[ℂ] E) := by
  set f : ℂ → ℂ := fun z ↦ (Y z).det
  set tr : (E →L[ℂ] E) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ))
  have htr : ∀ T : E →L[ℂ] E, tr T = LinearMap.trace ℂ E (T : E →ₗ[ℂ] E) := fun _ ↦ rfl
  have hf : MeromorphicAt f z₀ := caf_meromorphicAt_det hY
  have hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    filter_upwards [hunit] with z hz
    obtain ⟨u, hu⟩ := hz
    have hl : IsUnit (Y z : E →ₗ[ℂ] E) := by
      refine ⟨⟨u, ↑u⁻¹, ?_, ?_⟩, by rw [← hu]⟩ <;> ext v
      · change ((↑u : E →L[ℂ] E) * ↑u⁻¹) v = v
        rw [Units.mul_inv]; rfl
      · change ((↑u⁻¹ : E →L[ℂ] E) * ↑u) v = v
        rw [Units.inv_mul]; rfl
    exact (LinearMap.isUnit_det _ hl).ne_zero
  have htop : meromorphicOrderAt f z₀ ≠ ⊤ := by
    intro h
    obtain ⟨z, h1, h2⟩ := ((meromorphicOrderAt_eq_top_iff.1 h).and hne).exists
    exact h2 h1
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 htop
  refine ⟨m, hm.symm, ?_⟩
  have hode' : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • deriv f z =
      (tr A₀ • ContinuousLinearMap.id ℂ ℂ) (f z) +
        (z - z₀) • (tr (G z) • ContinuousLinearMap.id ℂ ℂ) (f z) := by
    filter_upwards [hode, hunit, self_mem_nhdsWithin] with z h1 h2 h3
    have hz : z - z₀ ≠ 0 := sub_ne_zero.2 h3
    rw [(caf_hasDerivAt_det h1 h2).deriv, ← htr, map_smul, map_add, map_smul]
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp
    rfl
  have hGc : ContinuousAt (fun z ↦ tr (G z) • ContinuousLinearMap.id ℂ ℂ) z₀ :=
    (tr.continuous.continuousAt.comp hG).smul continuousAt_const
  obtain ⟨v, hv, hAv⟩ := caf_order_eigenvalue f z₀ (tr A₀ • ContinuousLinearMap.id ℂ ℂ)
    (fun z ↦ tr (G z) • ContinuousLinearMap.id ℂ ℂ) m hf hm.symm hGc hode'
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at hAv
  rw [← htr]
  exact (mul_right_cancel₀ hv hAv).symm

theorem caf_rotation_order_aux (v : ℂ → E) (m : ℤ) (ζ α : ℂ) (hζ : ζ ≠ 0)
    (hv : MeromorphicAt v 0) (hm : meromorphicOrderAt v 0 = (m : WithTop ℤ))
    (hrot : ∀ᶠ y in 𝓝[≠] (0 : ℂ), v (ζ * y) = α • v y) :
    α = ζ ^ m := by
  obtain ⟨g, hg, hg0, hvg⟩ := (meromorphicOrderAt_eq_int_iff hv).1 hm
  have hmul : Tendsto (fun y : ℂ ↦ ζ * y) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.mul continuous_id : Continuous fun y : ℂ ↦ ζ * y).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact mul_ne_zero hζ hy
  have hev : ∀ᶠ y in 𝓝[≠] (0 : ℂ), ζ ^ m • g (ζ * y) = α • g y := by
    filter_upwards [hrot, hvg, hmul.eventually hvg, self_mem_nhdsWithin] with y h1 h2 h3 hy
    simp only [sub_zero] at h2 h3
    rw [h3, h2, mul_zpow, mul_comm (ζ ^ m), mul_smul, smul_comm α] at h1
    exact smul_right_injective E (zpow_ne_zero m (show y ≠ 0 from hy)) h1
  have hgc := hg.continuousAt
  have h1 : Tendsto (fun y ↦ ζ ^ m • g (ζ * y)) (𝓝[≠] (0 : ℂ)) (𝓝 (ζ ^ m • g 0)) := by
    refine Tendsto.const_smul ?_ _
    have : Tendsto (fun y : ℂ ↦ ζ * y) (𝓝[≠] 0) (𝓝 0) := hmul.mono_right nhdsWithin_le_nhds
    exact hgc.tendsto.comp this
  have h2 : Tendsto (fun y ↦ α • g y) (𝓝[≠] (0 : ℂ)) (𝓝 (α • g 0)) :=
    (hgc.tendsto.mono_left nhdsWithin_le_nhds).const_smul _
  have heq := tendsto_nhds_unique (h1.congr' hev) h2
  have : (ζ ^ m - α) • g 0 = 0 := by rw [sub_smul, heq, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact (sub_eq_zero.1 h).symm
  · exact absurd h hg0

theorem caf_isUnit_extension_aux [FiniteDimensional ℂ E] (Y H D : ℂ → E →L[ℂ] E) (z₀ : ℂ)
    (n : ℤ) (hH : AnalyticAt ℂ H z₀)
    (hYHD : ∀ᶠ z in 𝓝[≠] z₀, Y z = H z * D z)
    (hD : ∀ᶠ z in 𝓝[≠] z₀, (D z).det = (z - z₀) ^ n)
    (hdet : meromorphicOrderAt (fun z ↦ (Y z).det) z₀ = (n : WithTop ℤ)) :
    IsUnit (H z₀) := by
  have hh := caf_analyticAt_det hH
  have heq : (fun z ↦ (Y z).det) =ᶠ[𝓝[≠] z₀] fun z ↦ (H z).det * (z - z₀) ^ n := by
    filter_upwards [hYHD, hD] with z h1 h2
    rw [h1, ← h2]
    exact LinearMap.det_comp _ _
  have hlin : MeromorphicAt (fun z : ℂ ↦ z - z₀) z₀ :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hpow : meromorphicOrderAt (fun z ↦ (z - z₀) ^ n) z₀ = (n : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_zpow hlin, meromorphicOrderAt_id_sub_const]
    simp
  have hlinn : MeromorphicAt (fun z : ℂ ↦ (z - z₀) ^ n) z₀ := hlin.zpow n
  rw [meromorphicOrderAt_congr heq, fun_meromorphicOrderAt_mul hh.meromorphicAt hlinn,
    hpow] at hdet
  have h0 : meromorphicOrderAt (fun z ↦ (H z).det) z₀ = 0 := by
    cases h : meromorphicOrderAt (fun z ↦ (H z).det) z₀ with
    | top => rw [h] at hdet; simp at hdet
    | coe k =>
      rw [h] at hdet
      have : k + n = n := by exact_mod_cast hdet
      rw [show k = 0 by omega]; rfl
  apply caf_isUnit_of_det_ne_zero
  rw [hh.meromorphicOrderAt_eq] at h0
  have : analyticOrderAt (fun z ↦ (H z).det) z₀ = 0 := by
    cases h : analyticOrderAt (fun z ↦ (H z).det) z₀ with
    | top => rw [h] at h0; simp at h0
    | coe k => rw [h] at h0; simp at h0; rw [h0]; rfl
  rcases analyticOrderAt_eq_zero.1 this with h | h
  · exact absurd hh h
  · exact h

end HodgeLean.Foundations.Program
