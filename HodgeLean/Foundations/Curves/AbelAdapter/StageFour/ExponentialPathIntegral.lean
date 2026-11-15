import HodgeLean.Foundations.Program.CurveJacobianAExact
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set Metric
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Source: Forster, Lectures on Riemann Surfaces, §10, multiplicative path independence. -/
theorem exponential_pathIntegral_independent (θ : b3_HolForm E C)
    (hperiod : ∀ γ : b3_SmoothLoop E C, Complex.exp (b3_period E C γ θ) = 1)
    {p q : C} {γ δ : ℝ → C}
    (hγ : b3A_IsGoodPath (E := E) γ p q) (hδ : b3A_IsGoodPath (E := E) δ p q) :
    Complex.exp (b3_pathIntegral E C γ θ) = Complex.exp (b3_pathIntegral E C δ θ) := by
  have hloop := hγ.trans hδ.symm
  have he := hperiod (b3A_toLoop hloop)
  change Complex.exp (b3_pathIntegral E C (b3A_toLoop hloop).1 θ) = 1 at he
  rw [b3A_toLoop_pathIntegral, b3A_pathIntegral_trans θ.property hγ hδ.symm,
    b3A_pathIntegral_symm θ.property _ hδ.1] at he
  exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr (by simpa only [sub_eq_add_neg] using he)

/-- Source: Forster, Lectures on Riemann Surfaces, §10, exponentiation of abelian integrals. -/
theorem exponentialPrimitive_of_integralPeriods [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C) (θ : b3_HolForm E C)
    (hperiod : ∀ γ : b3_SmoothLoop E C, Complex.exp (b3_period E C γ θ) = 1) :
    ∃ F : C → ℂ, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω F ∧
      (∀ q, F q ≠ 0) ∧
      ∀ (q : C) (γ : ℝ → C), b3A_IsGoodPath (E := E) γ p q →
        F q = Complex.exp (b3_pathIntegral E C γ θ) := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ h
  let b := Module.finBasisOfFinrankEq ℂ E h
  let u := b 0
  let κ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord 0)
  have hκ : ∀ w : E, w = κ w • u := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    simp [κ, u]
  have hκu : κ u = 1 := by simp [κ, u]
  have hu : u ≠ 0 := b.ne_zero 0
  choose γp hγp using fun q : C => b3A_joined (E := E) p q
  let F : C → ℂ := fun q => Complex.exp (b3_pathIntegral E C (γp q) θ)
  have hindep (q : C) (γ : ℝ → C) (hγ : b3A_IsGoodPath (E := E) γ p q) :
      F q = Complex.exp (b3_pathIntegral E C γ θ) :=
    exponential_pathIntegral_independent θ hperiod (hγp q) hγ
  refine ⟨F, ?_, fun q => Complex.exp_ne_zero _, hindep⟩
  intro q
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u hu q
  obtain ⟨G, hG⟩ : Complex.IsExactOn (b3A_discCoef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) q u)
      (ball (0 : ℂ) R) :=
    DifferentiableOn.isExactOn_ball fun z hz => (b3A_discCoef_differentiableAt θ.property q u
      (hR z (mem_ball_zero_iff.mp hz))).differentiableWithinAt
  have hlocal (z : ℂ) (hz : ‖z‖ < R) :
      F (b3A_disc q u z) = F q * Complex.exp (G z - G 0) := by
    have hs := b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hz)
    rw [(chartAt E q).left_inv (mem_chart_source E q)] at hs
    change F ((chartAt E q).symm (chartAt E q q + z • u)) = _
    rw [hindep _ _ ((hγp q).trans hs),
      b3A_pathIntegral_trans θ.property (hγp q) hs,
      b3A_segment_integral θ.property κ u hκ hκu q hR hG z hz, Complex.exp_add]
  let ζ : C → ℂ := fun y => κ (chartAt E q y - chartAt E q q)
  have hζ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω ζ q := by
    have h1 := contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)
    have h2 : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun w : E => κ (w - chartAt E q q)) :=
      (κ.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
    exact (h2 _).comp q h1
  have hζ0 : ζ q = 0 := by simp [ζ]
  have hev : ∀ᶠ y in 𝓝 q, F y = F q * Complex.exp (G (ζ y) - G 0) := by
    have hU : (chartAt E q).source ∩ {y | ‖ζ y‖ < R} ∈ 𝓝 q := by
      refine inter_mem ((chartAt E q).open_source.mem_nhds (mem_chart_source E q)) ?_
      exact hζ.continuousAt.preimage_mem_nhds
        ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simp [hζ0, hR0]))
    filter_upwards [hU] with y hy
    have he : b3A_disc q u (ζ y) = y := by
      rw [b3A_disc, ← hκ, add_sub_cancel]
      exact (chartAt E q).left_inv hy.1
    simpa only [he] using hlocal (ζ y) hy.2
  have hGa : AnalyticAt ℂ G (ζ q) := by
    rw [hζ0]
    exact (show DifferentiableOn ℂ G (ball (0 : ℂ) R) from fun z hz =>
      (hG z hz).differentiableAt.differentiableWithinAt).analyticAt (ball_mem_nhds 0 hR0)
  have hGH : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G (ζ q) := hGa.contDiffAt.contMDiffAt
  have hexp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω Complex.exp := Complex.contDiff_exp.contMDiff
  apply ContMDiffAt.congr_of_eventuallyEq _ hev
  exact contMDiffAt_const.mul ((hexp _).comp q ((hGH.comp q hζ).sub contMDiffAt_const))

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
