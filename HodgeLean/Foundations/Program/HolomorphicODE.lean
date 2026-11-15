import HodgeLean.Foundations.Program.HolomorphicODEProofs

/-! # Holomorphic ODE and parameter integrals

Implication from analytic vector fields and explicit bounds to local analytic solutions,
and from continuous parameter-holomorphic integrands to analytic integrals.
No singular-pole, monodromy, Schlesinger normalization or geometric jet assertion is made.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric
open scoped Interval
namespace HodgeLean.Foundations.Program

/-- Existence on a specified positive time disc.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
theorem b65_holomorphic_ode (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ y : ℂ → E, AnalyticOnNhd ℂ y (ball x₀ (b65_radius R S M)) ∧
      y x₀ = y₀ ∧ MapsTo y (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
      ∀ x ∈ ball x₀ (b65_radius R S M), HasDerivAt y (A (x, y x)) x :=
  b65_holomorphic_ode_aux E A x₀ y₀ R S M hR hS hM hA hb

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ y : ℂ → E, AnalyticOnNhd ℂ y (ball x₀ (b65_radius R S M)) ∧
      y x₀ = y₀ ∧ MapsTo y (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
      ∀ x ∈ ball x₀ (b65_radius R S M), HasDerivAt y (A (x, y x)) x :=
  b65_holomorphic_ode E A x₀ y₀ R S M hR hS hM hA hb

/-- Uniqueness throughout the connected time disc.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
theorem b65_holomorphic_ode_unique (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (r S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hA : AnalyticOnNhd ℂ A (ball x₀ r ×ˢ ball y₀ S))
    (y z : ℂ → E) (hy₀ : y x₀ = y₀) (hz₀ : z x₀ = y₀)
    (hy : MapsTo y (ball x₀ r) (ball y₀ S))
    (hz : MapsTo z (ball x₀ r) (ball y₀ S))
    (hdy : ∀ x ∈ ball x₀ r, HasDerivAt y (A (x, y x)) x)
    (hdz : ∀ x ∈ ball x₀ r, HasDerivAt z (A (x, z x)) x) :
    EqOn y z (ball x₀ r) :=
  b65_holomorphic_ode_unique_aux E A x₀ y₀ r S hr hS hA y z hy₀ hz₀ hy hz hdy hdz

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (r S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hA : AnalyticOnNhd ℂ A (ball x₀ r ×ˢ ball y₀ S))
    (y z : ℂ → E) (hy₀ : y x₀ = y₀) (hz₀ : z x₀ = y₀)
    (hy : MapsTo y (ball x₀ r) (ball y₀ S))
    (hz : MapsTo z (ball x₀ r) (ball y₀ S))
    (hdy : ∀ x ∈ ball x₀ r, HasDerivAt y (A (x, y x)) x)
    (hdz : ∀ x ∈ ball x₀ r, HasDerivAt z (A (x, z x)) x) :
    EqOn y z (ball x₀ r) :=
  b65_holomorphic_ode_unique E A x₀ y₀ r S hr hS hA y z hy₀ hz₀ hy hz hdy hdz

/-- Joint analytic dependence on time and initial value.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
theorem b65_holomorphic_ode_initial (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ F : ℂ × E → E,
      AnalyticOnNhd ℂ F (ball x₀ (b65_radius R S M) ×ˢ ball y₀ (S / 2)) ∧
      ∀ v ∈ ball y₀ (S / 2), F (x₀, v) = v ∧
        MapsTo (fun x ↦ F (x, v)) (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
        ∀ x ∈ ball x₀ (b65_radius R S M),
          HasDerivAt (fun t ↦ F (t, v)) (A (x, F (x, v))) x :=
  b65_holomorphic_ode_initial_aux E A x₀ y₀ R S M hR hS hM hA hb

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ × E → E) (x₀ : ℂ) (y₀ : E) (R S M : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R ×ˢ ball y₀ S))
    (hb : ∀ q ∈ ball x₀ R ×ˢ ball y₀ S, ‖A q‖ ≤ M) :
    ∃ F : ℂ × E → E,
      AnalyticOnNhd ℂ F (ball x₀ (b65_radius R S M) ×ˢ ball y₀ (S / 2)) ∧
      ∀ v ∈ ball y₀ (S / 2), F (x₀, v) = v ∧
        MapsTo (fun x ↦ F (x, v)) (ball x₀ (b65_radius R S M)) (ball y₀ S) ∧
        ∀ x ∈ ball x₀ (b65_radius R S M),
          HasDerivAt (fun t ↦ F (t, v)) (A (x, F (x, v))) x :=
  b65_holomorphic_ode_initial E A x₀ y₀ R S M hR hS hM hA hb

/-- Joint analytic dependence on additional parameters with a uniform bound.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
theorem b65_holomorphic_ode_parameters (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
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
          HasDerivAt (fun t ↦ F (p, (t, v))) (A (p, (x, F (p, (x, v))))) x :=
  b65_holomorphic_ode_parameters_aux E P A p₀ x₀ y₀ ρ R S M hρ hR hS hM hA hb

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
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
          HasDerivAt (fun t ↦ F (p, (t, v))) (A (p, (x, F (p, (x, v))))) x :=
  b65_holomorphic_ode_parameters E P A p₀ x₀ y₀ ρ R S M hρ hR hS hM hA hb

/-- A fundamental operator solution on a disc without poles.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
theorem b65_linear_system (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (x₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R)) :
    ∃ Y : ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Y (ball x₀ R) ∧
      Y x₀ = ContinuousLinearMap.id ℂ E ∧
      (∀ x ∈ ball x₀ R, HasDerivAt Y ((A x).comp (Y x)) x) ∧
      ∀ x ∈ ball x₀ R, Function.Bijective (Y x) :=
  b65_linear_system_aux E A x₀ R hR hA

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (x₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hA : AnalyticOnNhd ℂ A (ball x₀ R)) :
    ∃ Y : ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Y (ball x₀ R) ∧
      Y x₀ = ContinuousLinearMap.id ℂ E ∧
      (∀ x ∈ ball x₀ R, HasDerivAt Y ((A x).comp (Y x)) x) ∧
      ∀ x ∈ ball x₀ R, Function.Bijective (Y x) :=
  b65_linear_system E A x₀ R hR hA

/-- Analytic dependence of a continuous compact-interval integral.
Source: Mathlib.Analysis.Calculus.ParametricIntervalIntegral; Cauchy integral formula on compact parameter sets. -/
theorem b65_parameter_integral_analytic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℝ × P → E) (U : Set P) (a b : ℝ) (hU : IsOpen U)
    (hc : ContinuousOn f (Set.uIcc a b ×ˢ U))
    (hf : ∀ t ∈ Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (t, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, f (t, z)) U :=
  b65_parameter_integral_analytic_aux E P f U a b hU hc hf

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℝ × P → E) (U : Set P) (a b : ℝ) (hU : IsOpen U)
    (hc : ContinuousOn f (Set.uIcc a b ×ˢ U))
    (hf : ∀ t ∈ Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (t, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, f (t, z)) U :=
  b65_parameter_integral_analytic E P f U a b hU hc hf

/-- Analytic dependence along a fixed continuously differentiable contour.
Source: Mathlib.Analysis.Calculus.ParametricIntervalIntegral; Cauchy integral formula on compact parameter sets. -/
theorem b65_contour_integral_analytic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℂ × P → E) (U : Set P) (a b : ℝ)
    (γ γ' : ℝ → ℂ) (hU : IsOpen U)
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hγ' : ContinuousOn γ' (Set.uIcc a b))
    (hdγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hc : ContinuousOn f ((γ '' Set.uIcc a b) ×ˢ U))
    (hf : ∀ w ∈ γ '' Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (w, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, γ' t • f (γ t, z)) U :=
  b65_contour_integral_analytic_aux E P f U a b γ γ' hU hγ hγ' hdγ hc hf

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (f : ℂ × P → E) (U : Set P) (a b : ℝ)
    (γ γ' : ℝ → ℂ) (hU : IsOpen U)
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hγ' : ContinuousOn γ' (Set.uIcc a b))
    (hdγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hc : ContinuousOn f ((γ '' Set.uIcc a b) ×ˢ U))
    (hf : ∀ w ∈ γ '' Set.uIcc a b, AnalyticOnNhd ℂ (fun z ↦ f (w, z)) U) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t in a..b, γ' t • f (γ t, z)) U :=
  b65_contour_integral_analytic E P f U a b γ γ' hU hγ hγ' hdγ hc hf

/-- Field-type check for the path continuity and base membership used by
`HodgeLean.Papers.g32r_PeriodMap`. This affine path is an input test.
Source: HodgeLean/Papers/G32DominanceDefs.lean, fields curve_cont and curve_zero. -/
example (V : Set (Fin 10 → ℂ)) (y₀ v : Fin 10 → ℂ)
    (hy₀ : y₀ ∈ V) (hv : v ≠ 0) :
    ∃ curve : ℂ → Fin 10 → ℂ,
      ContinuousAt curve 0 ∧ curve 0 ∈ V ∧ curve 1 ≠ curve 0 ∧
      ∀ x, HasDerivAt curve v x := by
  refine ⟨fun t ↦ y₀ + t • v, by fun_prop, by simpa using hy₀, ?_, ?_⟩
  · simpa using hv
  · intro x
    simpa using ((hasDerivAt_id x).smul_const v).const_add y₀

end HodgeLean.Foundations.Program
