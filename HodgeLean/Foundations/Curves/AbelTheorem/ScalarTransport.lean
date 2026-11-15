import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem scalar_equation_in_chart (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h) (f : C → ℂ) (x y : C)
    (hy : y ∈ (extChartAt 𝓘(ℂ, E) x).source)
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω f y)
    (hd : HasDerivAt (centeredScalar h f y)
      (HurwitzPrymRR_loc h w y 0 * f y) 0) :
    HasDerivAt (centeredScalar h f x)
      (HurwitzPrymRR_loc h w x (b4c_centeredCoordinate h x y) * f y)
      (b4c_centeredCoordinate h x y) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
  let L := b4cov_lineEquiv h
  let G := b4cov_expr E E (id : C → C) y x
  let T := b4cov_transport h h G (extChartAt 𝓘(ℂ, E) y y)
  let σ := b4c_centeredCoordinate h x y
  have hσ : extChartAt 𝓘(ℂ, E) x x + L σ = extChartAt 𝓘(ℂ, E) x y := by
    dsimp [σ, b4c_centeredCoordinate, L]
    rw [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  have hxy : (extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + L σ) = y := by
    rw [hσ, (extChartAt 𝓘(ℂ, E) x).left_inv hy]
  have hGan : AnalyticAt ℂ G (extChartAt 𝓘(ℂ, E) y y) :=
    b4cov_analyticAt_chart id contMDiff_id y x _ (mem_extChartAt_target y)
      (by rw [extChartAt_to_inv]; exact hy)
  have hTan : AnalyticAt ℂ T 0 := b4cov_transport_analyticAt h h hGan
  have hT0 : T 0 = 0 := b4cov_transport_zero h h _ _
  have hG' : fderiv ℂ G (extChartAt 𝓘(ℂ, E) y y) ≠ 0 := by
    refine (b4cov_mfderiv_ne_zero_iff_expr id contMDiff_id y x y
      (mem_extChartAt_source y) hy).1 ?_
    rw [mfderiv_id]
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact hv (congrArg (fun A : E →L[ℂ] E => A v) h0)
  have hT' : deriv T 0 ≠ 0 := by
    rw [b4cov_transport_deriv h h 0 (by simpa using hGan.differentiableAt)]
    simp only [map_zero, add_zero]
    intro h0
    apply hG'
    ext v
    have h1 : fderiv ℂ G (extChartAt 𝓘(ℂ, E) y y) (L 1) = 0 := by
      simpa only [L, map_zero, ContinuousLinearEquiv.apply_symm_apply] using congrArg L h0
    have hv : v = L.symm v • L 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
    rw [hv, map_smul, h1, smul_zero]
    rfl
  have haff : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω
      (fun z : ℂ => extChartAt 𝓘(ℂ, E) x x + L z) σ := by
    have hh : ContDiff ℂ ω (fun z : ℂ => extChartAt 𝓘(ℂ, E) x x + L z) :=
      contDiff_const.add L.contDiff
    exact hh.contMDiff.contMDiffAt
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, E)) (n := ω) x).contMDiffAt
    ((isOpen_extChartAt_target x).mem_nhds ((extChartAt 𝓘(ℂ, E) x).map_source hy))
  rw [← hσ] at hinv
  have hf' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω f
      ((extChartAt 𝓘(ℂ, E) x).symm (extChartAt 𝓘(ℂ, E) x x + L σ)) := by
    rw [hxy]
    exact hf
  have hcomp := hf'.comp σ (hinv.comp σ haff)
  have hdx : DifferentiableAt ℂ (centeredScalar h f x) σ :=
    hcomp.contDiffAt.differentiableAt (by simp)
  have he : (fun t => centeredScalar h f x (σ + T t)) =ᶠ[𝓝 0]
      centeredScalar h f y := by
    have hcy : ContinuousAt (fun t : ℂ => (extChartAt 𝓘(ℂ, E) y).symm
        (extChartAt 𝓘(ℂ, E) y y + L t)) 0 := by
      have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, E)) (n := ω) y).contMDiffAt
        ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
      have hi' : ContinuousAt (extChartAt 𝓘(ℂ, E) y).symm
          (extChartAt 𝓘(ℂ, E) y y + L 0) := by
        simpa only [map_zero, add_zero] using hi.continuousAt
      exact ContinuousAt.comp (f := fun t : ℂ => extChartAt 𝓘(ℂ, E) y y + L t)
        (g := (extChartAt 𝓘(ℂ, E) y).symm) hi'
        ((continuous_const.add L.continuous).continuousAt (x := 0))
    have hn : ∀ᶠ t in 𝓝 (0 : ℂ), (extChartAt 𝓘(ℂ, E) y).symm
        (extChartAt 𝓘(ℂ, E) y y + L t) ∈ (extChartAt 𝓘(ℂ, E) x).source := by
      apply hcy.preimage_mem_nhds
      simpa only [map_zero, add_zero, extChartAt_to_inv] using
        (isOpen_extChartAt_source x).mem_nhds hy
    filter_upwards [hn] with t ht
    have hG0 : G (extChartAt 𝓘(ℂ, E) y y) = extChartAt 𝓘(ℂ, E) x y := by
      change (extChartAt 𝓘(ℂ, E) x)
        ((extChartAt 𝓘(ℂ, E) y).symm (extChartAt 𝓘(ℂ, E) y y)) = _
      rw [extChartAt_to_inv]
    have hc : extChartAt 𝓘(ℂ, E) x x + L (σ + T t) =
        G (extChartAt 𝓘(ℂ, E) y y + L t) := by
      rw [map_add]
      dsimp only [T, b4cov_transport]
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply, hG0]
      rw [← hσ]
      abel
    change f ((extChartAt 𝓘(ℂ, E) x).symm
      (extChartAt 𝓘(ℂ, E) x x + L (σ + T t))) = _
    rw [hc]
    exact congrArg f ((extChartAt 𝓘(ℂ, E) x).left_inv ht)
  have hdxx : HasDerivAt (centeredScalar h f x)
      (deriv (centeredScalar h f x) σ) (σ + T 0) := by
    simpa only [hT0, add_zero] using hdx.hasDerivAt
  have hchain := hdxx.comp 0 ((hTan.differentiableAt.hasDerivAt).const_add σ)
  have hcoef := HurwitzPrymRR_loc_pullback h h id contMDiff_id y x hy w w.property.1
  rw [HurwitzPrymRR_pullback_id] at hcoef
  have hvalue : HurwitzPrymRR_loc h w y 0 =
      HurwitzPrymRR_loc h w x σ * deriv T 0 := by
    simpa only [T, G, σ, b4c_centeredCoordinate, id_eq, hT0, add_zero] using hcoef.eq_of_nhds
  have heder := (hchain.congr_of_eventuallyEq he.symm).unique hd
  rw [hvalue] at heder
  have hv : deriv (centeredScalar h f x) σ = HurwitzPrymRR_loc h w x σ * f y := by
    apply mul_right_cancel₀ hT'
    calc
      deriv (centeredScalar h f x) σ * deriv T 0 =
          (HurwitzPrymRR_loc h w x σ * deriv T 0) * f y := heder
      _ = (HurwitzPrymRR_loc h w x σ * f y) * deriv T 0 := by ring
  rw [← hv]
  exact hdx.hasDerivAt

end HodgeLean.Foundations.Curves.AbelTheorem
