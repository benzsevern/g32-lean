import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! # Continuity of finite complex linear chart transitions

The operator topology is controlled by pointwise evaluation on the finite model fibre.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle TopologicalSpace
namespace HodgeLean.Foundations.BundleThom

/-- Linear trivializations with finite complex model have continuous operator-valued transitions.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, vector bundle transitions. -/
theorem i1_linearChartTransition_continuousOn
    {B : Type*} [TopologicalSpace B] (k : ℕ) (E : B → Type*)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] :
    ContinuousOn (fun b => (e.coordChangeL ℂ e' b : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)))
      (e.baseSet ∩ e'.baseSet) := by
  apply continuousOn_clm_apply.mpr
  intro v
  have hprod : Continuous (fun b : B => (b, v)) := continuous_id.prodMk continuous_const
  have h₁ : ContinuousOn
      (fun b => e.toOpenPartialHomeomorph.symm (b, v)) (e.baseSet ∩ e'.baseSet) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp hprod.continuousOn
      (fun b (hb : b ∈ e.baseSet ∩ e'.baseSet) => e.mem_target.mpr hb.1)
  have h₂ : ContinuousOn
      (fun b => (e' (e.toOpenPartialHomeomorph.symm (b, v))).2) (e.baseSet ∩ e'.baseSet) := by
    apply (e'.continuousOn.comp h₁ _).snd
    intro b hb
    apply e'.mem_source.mpr
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  exact h₂.congr (fun b hb => (congrArg Prod.snd (e.apply_symm_apply_eq_coordChangeL (R := ℂ) e' hb v)).symm)

end HodgeLean.Foundations.BundleThom
