import HodgeLean.Foundations.Program.CurveJacobianATorus

/-! # Track B3, lane A: loops on a torus

A `C¹` path on B2's torus develops into the universal cover, `γ t = γ 0 + [∫₀ᵗ γ']`; hence the
periods of a `C¹` loop on a compact connected torus are values of the form on lattice vectors.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section TorusLoops

variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
  [DiscreteTopology (b2_latticeMap Λ F).range] [IsManifold 𝓘(ℂ, b3A_TM F) ω (b2_torus Λ F)]

/-- On the torus, a `C¹` path read in any chart has derivative its velocity. -/
theorem b3A_torus_hasDerivAt_chart (γ : ℝ → b2_torus Λ F)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3A_TM F) 1 γ) (x₀ : b2_torus Λ F) (t : ℝ)
    (ht : γ t ∈ (chartAt (b3A_TM F) x₀).source) :
    HasDerivAt (chartAt (b3A_TM F) x₀ ∘ γ) (b3A_vel (E := b3A_TM F) (C := b2_torus Λ F) γ t) t := by
  obtain ⟨hd, he⟩ := b3A_chart_comp γ t (hγ t) x₀ ht
  have := (hd.differentiableAt one_ne_zero).hasFDerivAt.hasDerivAt
  rw [he, b3A_torus_fderiv_transition F x₀ (γ t) ht] at this
  exact this

/-- On the torus, the velocity of a `C¹` path is continuous. -/
theorem b3A_torus_velocity_continuous (γ : ℝ → b2_torus Λ F)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3A_TM F) 1 γ) :
    Continuous (b3A_vel (E := b3A_TM F) (C := b2_torus Λ F) γ) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set x₀ := γ t₀
  set U := γ ⁻¹' (chartAt (b3A_TM F) x₀).source
  have hU : IsOpen U := (chartAt (b3A_TM F) x₀).open_source.preimage hγ.continuous
  have ht₀ : t₀ ∈ U := mem_chart_source (b3A_TM F) x₀
  have hcd : ContDiffOn ℝ 1 (chartAt (b3A_TM F) x₀ ∘ γ) U := fun t ht ↦
    (b3A_chart_comp γ t (hγ t) x₀ ht).1.contDiffWithinAt
  have hcont : ContinuousOn (fun t ↦ fderiv ℝ (chartAt (b3A_TM F) x₀ ∘ γ) t 1) U :=
    (hcd.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  refine (hcont.continuousAt (hU.mem_nhds ht₀)).congr ?_
  filter_upwards [hU.mem_nhds ht₀] with t ht
  rw [(b3A_torus_hasDerivAt_chart F γ hγ x₀ t ht).hasFDerivAt.fderiv]
  exact one_smul ℝ _

/-- **Developing a path into the universal cover**: `γ t = γ 0 + [∫₀ᵗ γ']`. -/
theorem b3A_torus_develop (γ : ℝ → b2_torus Λ F)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3A_TM F) 1 γ) (t : ℝ) :
    γ t = γ 0 + QuotientAddGroup.mk ((b2_coord _).symm
      (∫ τ in (0 : ℝ)..t, b3A_vel (E := b3A_TM F) (C := b2_torus Λ F) γ τ)) := by
  set W : ℝ → b3A_TM F := fun t ↦ ∫ τ in (0 : ℝ)..t, b3A_vel (E := b3A_TM F) (C := b2_torus Λ F) γ τ
  have hv := b3A_torus_velocity_continuous F γ hγ
  have hW : ∀ t, HasDerivAt W (b3A_vel (E := b3A_TM F) (C := b2_torus Λ F) γ t) t := fun t ↦
    hv.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  set H : ℝ → b2_torus Λ F := fun t ↦ γ t - QuotientAddGroup.mk ((b2_coord _).symm (W t))
  have hloc : IsLocallyConstant H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    set x₀ := γ t₀
    set U := γ ⁻¹' (chartAt (b3A_TM F) x₀).source
    have hU : IsOpen U := (chartAt (b3A_TM F) x₀).open_source.preimage hγ.continuous
    have ht₀ : t₀ ∈ U := mem_chart_source (b3A_TM F) x₀
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU t₀ ht₀
    set c := chartAt (b3A_TM F) x₀ ∘ γ
    have hconst : ∀ t ∈ Metric.ball t₀ r, c t - W t = c t₀ - W t₀ := by
      intro t ht
      refine Metric.isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := fun t ↦ c t - W t)
        (convex_ball t₀ r).isPreconnected ?_ ?_ ht (Metric.mem_ball_self hr)
      · intro s hs
        exact ((b3A_torus_hasDerivAt_chart F γ hγ x₀ s (hball hs)).sub
          (hW s)).differentiableAt.differentiableWithinAt
      · intro s hs
        exact ((b3A_torus_hasDerivAt_chart F γ hγ x₀ s (hball hs)).sub (hW s)).deriv.trans
          (sub_self _)
    have hγc : ∀ t ∈ U, γ t = QuotientAddGroup.mk ((b2_coord _).symm (c t)) := by
      intro t ht
      rw [show (QuotientAddGroup.mk ((b2_coord _).symm (c t)) : b2_torus Λ F) =
        QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm (c t)) from rfl,
        ← b2t_torusChart_symm_apply F x₀]
      exact ((chartAt (b3A_TM F) x₀).left_inv ht).symm
    filter_upwards [Metric.ball_mem_nhds t₀ hr] with t ht
    simp only [H]
    rw [hγc t (hball ht), hγc t₀ ht₀, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub,
      ← map_sub, ← map_sub, hconst t ht]
  have := hloc.apply_eq_of_preconnectedSpace t 0
  simp only [H, W, intervalIntegral.integral_same, map_zero, QuotientAddGroup.mk_zero,
    sub_zero] at this
  rw [← this]
  abel

/-- **Periods of loops on a compact torus lie in the lattice**: the period of a `C¹` loop on a
holomorphic form `θ` is the value of `θ` on a lattice vector. -/
theorem b3A_torus_loop_period [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)]
    (γ : ℝ → b2_torus Λ F) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3A_TM F) 1 γ) (hper : γ 1 = γ 0)
    (θ : b3_HolForm (b3A_TM F) (b2_torus Λ F)) :
    ∃ x : Λ, b3_pathPeriod (b3A_TM F) (b2_torus Λ F) γ θ =
      b3A_formFunctional F θ (b2_coord _ (b2_latticeMap Λ F x)) := by
  have hd := b3A_torus_develop F γ hγ 1
  rw [hper, left_eq_add] at hd
  obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff _).1 hd
  refine ⟨x, ?_⟩
  rw [hx, LinearEquiv.apply_symm_apply]
  simp only [b3_pathPeriod, b3_pathIntegral]
  rw [b3A_torus_form_eq F θ]
  have hv := b3A_torus_velocity_continuous F γ hγ
  have := (LinearMap.toContinuousLinearMap (b3A_formFunctional F θ)).intervalIntegral_comp_comm
    (hv.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  exact this

end TorusLoops

end HodgeLean.Foundations.Program
