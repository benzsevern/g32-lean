import Mathlib.Analysis.Complex.Basic
import HodgeLean.Foundations.Program.G32Native.AbelSheetInverse
import Mathlib.Analysis.Analytic.Composition

/-! # Pulling a target coefficient chart onto its original sheet -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program.G32Native
variable {X Y E V : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The original sheet has an analytic inverse of the target coefficient chart. -/
theorem sheet_coefficient_inverse (f : X → Y) (x : X)
    (e : OpenPartialHomeomorph X E) (C : OpenPartialHomeomorph Y E) (b : OpenPartialHomeomorph Y V)
    (D : X → E) (he : x ∈ e.source) (hC : f x ∈ C.source)
    (hb : f x ∈ b.source) (hb0 : b (f x) = 0) (hf : ContinuousAt f x)
    (hcoord : e =ᶠ[𝓝 x] C ∘ f)
    (ha : AnalyticAt ℂ (D ∘ e.symm) (e x))
    (ha' : AnalyticAt ℂ (C ∘ b.symm) 0) :
    ∃ s : V → X, s 0 = x ∧ ContinuousAt s 0 ∧
      AnalyticAt ℂ (D ∘ s) 0 ∧
      (∀ᶠ c in 𝓝 (0 : V), f (s c) = b.symm c) := by
  have hex : e x = C (f x) := hcoord.self_of_nhds
  have hbI : b.symm 0 = f x := by rw [← hb0]; exact b.left_inv hb
  have ht0 : (C ∘ b.symm) 0 = e x := by simp only [Function.comp_apply, hbI, hex]
  have ht : ContinuousAt (C ∘ b.symm) 0 := ha'.continuousAt
  let s : V → X := e.symm ∘ (C ∘ b.symm)
  have hs0 : s 0 = x := by change e.symm ((C ∘ b.symm) 0) = x; rw [ht0, e.left_inv he]
  have hsc : ContinuousAt s 0 :=
    (e.continuousAt_symm (e.map_source he)).comp_of_eq ht ht0
  refine ⟨s, hs0, hsc, ?_, ?_⟩
  · have ha0 : AnalyticAt ℂ (D ∘ e.symm) ((C ∘ b.symm) 0) := by
      rw [ht0]
      exact ha
    exact ha0.comp ha'
  · have hten : Tendsto (C ∘ b.symm) (𝓝 0) (𝓝 (e x)) := by
      simpa only [ht0] using ht.tendsto
    have hsinv := (sheet_chart_inverse_germ f x e C he hC hf hcoord).comp_tendsto
        hten
    have hbt : (0 : V) ∈ b.target := hb0 ▸ b.map_source hb
    have hCb : ∀ᶠ c in 𝓝 (0 : V), b.symm c ∈ C.source :=
      (show Tendsto b.symm (𝓝 0) (𝓝 (f x)) by
        simpa only [hbI] using (b.continuousAt_symm hbt).tendsto)
        (C.open_source.mem_nhds hC)
    filter_upwards [hsinv, hCb] with c hc hcC
    exact hc.trans (C.left_inv hcC)

#print axioms sheet_coefficient_inverse
end HodgeLean.Foundations.Program.G32Native
