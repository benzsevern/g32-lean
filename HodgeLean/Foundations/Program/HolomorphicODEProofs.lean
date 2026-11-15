import HodgeLean.Foundations.Program.HolomorphicODEDefs
import HodgeLean.Foundations.Program.HolomorphicODELocal
import HodgeLean.Foundations.Program.HolomorphicODELinearGlobal
import HodgeLean.Foundations.Program.HolomorphicODEIntegral
import HodgeLean.Foundations.Program.HolomorphicODEEstimates
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RealDeriv

/-! # Open bodies for the holomorphic ODE draft -/

noncomputable section
open Set Metric Filter Topology
open scoped Interval
namespace HodgeLean.Foundations.Program

theorem b65_holomorphic_ode_unique_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (r S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hA : AnalyticOnNhd ℂ A (ball x₀ r ×ˢ ball y₀ S))
    (y z : ℂ → E) (hy₀ : y x₀ = y₀) (hz₀ : z x₀ = y₀)
    (hy : MapsTo y (ball x₀ r) (ball y₀ S))
    (hz : MapsTo z (ball x₀ r) (ball y₀ S))
    (hdy : ∀ x ∈ ball x₀ r, HasDerivAt y (A (x, y x)) x)
    (hdz : ∀ x ∈ ball x₀ r, HasDerivAt z (A (x, z x)) x) :
    EqOn y z (ball x₀ r) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hq₀ : (x₀, y₀) ∈ ball x₀ r ×ˢ ball y₀ S := ⟨hx₀, mem_ball_self hS⟩
  obtain ⟨K, T, hT, hLip⟩ :=
    (show ContDiffAt ℂ 1 A (x₀, y₀) from (hA _ hq₀).contDiffAt).exists_lipschitzOnWith
  have hyv : ContinuousAt y x₀ := (hdy x₀ hx₀).continuousAt
  have hzv : ContinuousAt z x₀ := (hdz x₀ hx₀).continuousAt
  have ht : Tendsto (fun t : ℝ ↦ x₀ + (t : ℂ)) (𝓝 0) (𝓝 x₀) := by
    have hh : ContinuousAt (fun t : ℝ ↦ x₀ + (t : ℂ)) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, add_zero] using hh.tendsto
  have hyt : ∀ᶠ t : ℝ in 𝓝 0, (x₀ + (t : ℂ), y (x₀ + (t : ℂ))) ∈ T := by
    have hh := ht.prodMk_nhds (hyv.tendsto.comp ht)
    apply hh.eventually
    simpa [hy₀] using hT
  have hzt : ∀ᶠ t : ℝ in 𝓝 0, (x₀ + (t : ℂ), z (x₀ + (t : ℂ))) ∈ T := by
    have hh := ht.prodMk_nhds (hzv.tendsto.comp ht)
    apply hh.eventually
    simpa [hz₀] using hT
  have htime : ∀ᶠ t : ℝ in 𝓝 0, x₀ + (t : ℂ) ∈ ball x₀ r :=
    ht.eventually (ball_mem_nhds x₀ hr)
  have hder (w : ℂ → E)
      (hw : ∀ x ∈ ball x₀ r, HasDerivAt w (A (x, w x)) x)
      (t : ℝ) (htm : x₀ + (t : ℂ) ∈ ball x₀ r) :
      HasDerivAt (fun u : ℝ ↦ w (x₀ + (u : ℂ)))
        (A (x₀ + (t : ℂ), w (x₀ + (t : ℂ)))) t := by
    have hh := (hw _ htm).scomp t (Complex.ofRealCLM.hasDerivAt.const_add x₀)
    simpa [Function.comp_def] using hh
  have heq : (fun t : ℝ ↦ y (x₀ + (t : ℂ))) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ z (x₀ + (t : ℂ))) := by
    apply ODE_solution_unique_of_eventually
      (v := fun t v ↦ A (x₀ + (t : ℂ), v))
      (s := fun t ↦ {v | (x₀ + (t : ℂ), v) ∈ T}) (K := K)
    · exact Eventually.of_forall fun t v hv w hw ↦ by
        simpa only [Prod.edist_eq, edist_self, max_eq_right zero_le] using hLip hv hw
    · filter_upwards [htime, hyt] with t ht' hy'
      exact ⟨hder y hdy t ht', hy'⟩
    · filter_upwards [htime, hzt] with t ht' hz'
      exact ⟨hder z hdz t ht', hz'⟩
    · simpa using hy₀.trans hz₀.symm
  have hp : Tendsto (fun t : ℝ ↦ x₀ + (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] x₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht.mono_left inf_le_left, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht'
    simpa using ht'
  apply ((show DifferentiableOn ℂ y (ball x₀ r) from
    fun x hx ↦ (hdy x hx).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
    ).eqOn_of_preconnected_of_frequently_eq
      ((show DifferentiableOn ℂ z (ball x₀ r) from
        fun x hx ↦ (hdz x hx).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball)
      (convex_ball x₀ r).isPreconnected hx₀
  have heqp : ∀ᶠ t : ℝ in 𝓝[≠] 0, y (x₀ + (t : ℂ)) = z (x₀ + (t : ℂ)) :=
    heq.filter_mono inf_le_left
  exact hp.frequently heqp.frequently

theorem b65_holomorphic_ode_parameters_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (A : P × (ℂ × E) → E) (p₀ : P) (x₀ : ℂ) (y₀ : E) (ρ R S M : ℝ)
    (hρ : 0 < ρ) (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball p₀ ρ ×ˢ (ball x₀ R ×ˢ ball y₀ S)))
    (hb : ∀ q ∈ ball p₀ ρ ×ˢ (ball x₀ R ×ˢ ball y₀ S), ‖A q‖ ≤ M) :
    ∃ F : P × (ℂ × E) → E,
      AnalyticOnNhd ℂ F
        (ball p₀ ρ ×ˢ (ball x₀ (b65_radius R S M) ×ˢ ball y₀ (S / 2))) ∧
      ∀ p ∈ ball p₀ ρ, ∀ v ∈ ball y₀ (S / 2), F (p, (x₀, v)) = v ∧
        MapsTo (fun x ↦ F (p, (x, v))) (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
        ∀ x ∈ ball x₀ (b65_radius R S M),
          HasDerivAt (fun t ↦ F (p, (t, v))) (A (p, (x, F (p, (x, v))))) x := by
  have ht : ball x₀ (b65_radius R S M) ⊆ ball x₀ R :=
    ball_subset_ball (b65_radius_le_half.trans (by linarith))
  have hsub : ball p₀ ρ ×ˢ (ball x₀ (b65_radius R S M) ×ˢ ball y₀ S) ⊆
      ball p₀ ρ ×ˢ (ball x₀ R ×ˢ ball y₀ S) :=
    fun q hq ↦ ⟨hq.1, ht hq.2.1, hq.2.2⟩
  exact b65_local_parameter_solution isOpen_ball (b65_radius_pos hR hS hM) hS hM
    (b65_radius_displacement_lt hR hS hM)
    (K := M / (M + 1)) (by positivity)
    ((div_lt_one (by positivity : 0 < M + 1)).mpr (by linarith))
    (b65_radius_contraction_le hS hM) (hA.mono hsub) (fun q hq ↦ hb q (hsub hq))

theorem b65_holomorphic_ode_initial_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ F : ℂ × E → E,
      AnalyticOnNhd ℂ F (ball x₀ (b65_radius R S M) ×ˢ ball y₀ (S / 2)) ∧
      ∀ v ∈ ball y₀ (S / 2), F (x₀, v) = v ∧
        MapsTo (fun x ↦ F (x, v)) (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
        ∀ x ∈ ball x₀ (b65_radius R S M),
          HasDerivAt (fun t ↦ F (t, v)) (A (x, F (x, v))) x := by
  have hAp : AnalyticOnNhd ℂ (fun q : ℂ × (ℂ × E) ↦ A q.2)
      (ball 0 1 ×ˢ (ball x₀ R ×ˢ ball y₀ S)) := by
    intro q hq
    exact (hA q.2 hq.2).comp analyticAt_snd
  obtain ⟨F, hF, hs⟩ := b65_holomorphic_ode_parameters_aux E ℂ
    (fun q ↦ A q.2) 0 x₀ y₀ 1 R S M zero_lt_one hR hS hM hAp
    (fun q hq ↦ hb q.2 hq.2)
  refine ⟨fun q ↦ F (0, q), ?_, ?_⟩
  · intro q hq
    exact (hF (0, q) ⟨mem_ball_self zero_lt_one, hq⟩).comp
      (analyticAt_const.prod analyticAt_id)
  · exact hs 0 (mem_ball_self zero_lt_one)

theorem b65_holomorphic_ode_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ y : ℂ → E, AnalyticOnNhd ℂ y (ball x₀ (b65_radius R S M)) ∧
      y x₀ = y₀ ∧ MapsTo y (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
      ∀ x ∈ ball x₀ (b65_radius R S M), HasDerivAt y (A (x, y x)) x := by
  obtain ⟨F, hF, hs⟩ := b65_holomorphic_ode_initial_aux E A x₀ y₀ R S M hR hS hM hA hb
  have hy₀ : y₀ ∈ ball y₀ (S / 2) := mem_ball_self (half_pos hS)
  obtain ⟨hinit, hmaps, hder⟩ := hs y₀ hy₀
  refine ⟨fun x ↦ F (x, y₀), ?_, hinit, hmaps, hder⟩
  intro x hx
  exact (hF (x, y₀) ⟨hx, hy₀⟩).curry_left

theorem b65_linear_system_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (x₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R)) :
    ∃ Y : ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Y (ball x₀ R) ∧
      Y x₀ = ContinuousLinearMap.id ℂ E ∧
      (∀ x ∈ ball x₀ R, HasDerivAt Y ((A x).comp (Y x)) x) ∧
      ∀ x ∈ ball x₀ R, Function.Bijective (Y x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let L := ContinuousLinearMap.compL ℂ E E E
  have hL : AnalyticOnNhd ℂ (fun x ↦ L (A x)) (ball x₀ R) := by
    intro x hx
    exact (L.analyticAt (A x)).comp (hA x hx)
  obtain ⟨Y, hY, hY₀, hdY⟩ := b65_global_linear_solution (ContinuousLinearMap.id ℂ E) hL
  have hR' : AnalyticOnNhd ℂ (fun x ↦ -(L.flip (A x))) (ball x₀ R) := by
    intro x hx
    have hh := ((L.flip.analyticAt (A x)).comp (hA x hx)).neg
    convert hh using 1
    funext t
    simp only [Function.comp_def, Pi.neg_apply]
  obtain ⟨Z, hZ, hZ₀, hdZ⟩ := b65_global_linear_solution (ContinuousLinearMap.id ℂ E) hR'
  have hdy (x : ℂ) (hx : x ∈ ball x₀ R) : HasDerivAt Y ((A x).comp (Y x)) x := by
    simpa [L] using hdY x hx
  have hdz (x : ℂ) (hx : x ∈ ball x₀ R) : HasDerivAt Z (-((Z x).comp (A x))) x := by
    simpa [L] using hdZ x hx
  have hprod (x : ℂ) (hx : x ∈ ball x₀ R) : HasDerivAt (fun t ↦ (Z t).comp (Y t)) 0 x := by
    simpa [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc] using (hdz x hx).clm_comp (hdy x hx)
  have hleft (x : ℂ) (hx : x ∈ ball x₀ R) : (Z x).comp (Y x) = ContinuousLinearMap.id ℂ E := by
    have hh := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x₀ R).isPreconnected
      (show DifferentiableOn ℂ (fun t ↦ (Z t).comp (Y t)) (ball x₀ R) from
        fun t ht ↦ (hprod t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hprod t ht).deriv) hx (mem_ball_self hR)
    simpa [hY₀, hZ₀] using hh
  refine ⟨Y, hY, hY₀, hdy, fun x hx ↦ ?_⟩
  have hinj : Function.Injective (Y x) := by
    intro v w hvw
    have hh : Z x (Y x v) = v := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun f : E →L[ℂ] E ↦ f v) (hleft x hx)
    have hh' : Z x (Y x w) = w := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun f : E →L[ℂ] E ↦ f w) (hleft x hx)
    exact hh.symm.trans ((congrArg (Z x) hvw).trans hh')
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (Y x).toLinearMap)).mp hinj⟩

theorem b65_parameter_integral_analytic_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℝ × P → E) (U : Set P) (a b : ℝ) (hU : IsOpen U)
    (hc : ContinuousOn f (Set.uIcc a b ×ˢ U))
    (hf : ∀ t ∈ Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (t, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, f (t, z)) U := by
  exact b65_parameter_integral_analytic_mathlib E P f U a b hU hc hf

theorem b65_contour_integral_analytic_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℂ × P → E) (U : Set P) (a b : ℝ)
    (γ γ' : ℝ → ℂ) (hU : IsOpen U)
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hγ' : ContinuousOn γ' (Set.uIcc a b))
    (hdγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hc : ContinuousOn f ((γ '' Set.uIcc a b) ×ˢ U))
    (hf : ∀ w ∈ γ '' Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (w, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, γ' t • f (γ t, z)) U := by
  apply b65_parameter_integral_analytic_aux E P
    (fun q : ℝ × P ↦ γ' q.1 • f (γ q.1, q.2)) U a b hU
  · have ht : ContinuousOn (fun q : ℝ × P ↦ γ' q.1)
        (Set.uIcc a b ×ˢ U) :=
      hγ'.comp continuousOn_fst (fun _ hq ↦ hq.1)
    have hg : ContinuousOn (fun q : ℝ × P ↦ (γ q.1, q.2))
        (Set.uIcc a b ×ˢ U) :=
      (hγ.comp continuousOn_fst (fun _ hq ↦ hq.1)).prodMk continuousOn_snd
    exact ht.smul (hc.comp hg (fun q hq ↦ ⟨⟨q.1, hq.1, rfl⟩, hq.2⟩))
  · intro t ht z hz
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : P ↦ γ' t) z).smul (hf (γ t) ⟨t, ht, rfl⟩ z hz)

end HodgeLean.Foundations.Program
