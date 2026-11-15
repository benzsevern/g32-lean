import HodgeLean.Foundations.Program.PrymVariationFramesDefs
import HodgeLean.Foundations.Program.PrymVariationFramesMoving

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b63e_analytic_on_span {H E : Type*} [AddCommGroup H] [hH : Module ℤ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (P : H →ₗ[ℤ] (E → ℂ))
    (S : Set H) (hS : Submodule.span ℤ S = ⊤) (U : Set E)
    (hP : ∀ x ∈ S, AnalyticOnNhd ℂ (P x) U) (x : H) :
    AnalyticOnNhd ℂ (P x) U := by
  have hi : hH = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  cases hi
  have hx : x ∈ Submodule.span ℤ S := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hP y hy
  | zero =>
    rw [map_zero]
    change AnalyticOnNhd ℂ (fun _ : E ↦ (0 : ℂ)) U
    exact analyticOnNhd_const
  | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
  | smul k x _ hx =>
    rw [map_smul]
    have h := hx.const_smul (c := (k : ℂ))
    convert h using 1
    ext u
    simp only [Pi.smul_apply, Int.cast_smul_eq_zsmul]

set_option backward.isDefEq.respectTransparency false in
def b63e_periodFunctionLinear (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm b C V hV U) (s : V) :
    b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ] ((Fin 10 → ℂ) → ℂ) where
  toFun := b63e_periodFunction b C V hV P θ s
  map_add' := by
    intro x y
    funext u
    by_cases hu : u ∈ V
    · simp [b63e_periodFunction, hu, LinearEquiv.map_smul, map_smul]
    · simp [b63e_periodFunction, hu, LinearEquiv.map_smul, map_smul]
  map_smul' := by
    intro k x
    funext u
    by_cases hu : u ∈ V
    · simp [b63e_periodFunction, hu, LinearEquiv.map_smul, map_smul]
    · simp [b63e_periodFunction, hu, LinearEquiv.map_smul, map_smul]

theorem b63e_loop_period_analytic (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (s : V)
    (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s)) :
    AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s (b6m_loopClass _ γ)) (V ∩ U) := by
  classical
  intro u₀ hu₀
  have hc : Continuous fun τ ↦ (γ.1 τ).val.2 :=
    continuous_snd.comp (continuous_subtype_val.comp γ.2.2.continuous)
  have hcp : Function.Periodic (fun τ ↦ (γ.1 τ).val.2) 1 := fun τ ↦ by
    change (γ.1 (τ + 1)).val.2 = (γ.1 τ).val.2
    rw [γ.2.1 τ]
  have key := b63e_fibre_period_analyticAt b C V hV hVo hA hincl P hP U hU θ ⟨u₀, hu₀.1⟩ hu₀.2
    hc hcp
  refine key.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  by_cases hu : u ∈ V
  · have e : b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨u, hV hu⟩)
        (b6m_loopClass _ γ) = b63e_fibreLoopClass b C ⟨u, hV hu⟩ hc hcp := by
      have h1 := b63e_loopClass_eq_fibreLoopClass_param b C V hV s γ
      have h2 := b63e_fibreLoopClass_transport b C ⟨s.val, hV s.property⟩ ⟨u, hV hu⟩ hc hcp
      exact (congrArg (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨u, hV hu⟩))
        h1).trans h2
    simp only [b63e_periodFunction, hu, ↓reduceDIte, e]
  · simp only [b63e_periodFunction, hu, ↓reduceDIte]

set_option backward.isDefEq.respectTransparency false in
theorem b63e_period_analytic_of_loops (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm b C V hV U) (s : V)
    [T2Space (b63l_parameterFibre b C V hV s)]
    [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hloop : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s (b6m_loopClass _ γ)) (V ∩ U))
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s x) (V ∩ U) := by
  apply b63e_analytic_on_span (b63e_periodFunctionLinear b C V hV P θ s)
    (Set.range (b6m_loopClass (b63l_parameterFibre b C V hV s)))
    (b6m_smooth_loops_span _) (V ∩ U)
  rintro _ ⟨γ, rfl⟩
  exact hloop γ

end HodgeLean.Foundations.Program
