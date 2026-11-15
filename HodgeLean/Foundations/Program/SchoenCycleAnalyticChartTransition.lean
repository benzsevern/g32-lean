import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Composition

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Analyticity of two chart comparisons with a common chart gives their actual analytic transition.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Gunning and Rossi, Analytic Functions of Several Complex Variables, Chapter I. -/
theorem s2e_analytic_chart_transition
    {X : Type*} [TopologicalSpace X] (n : ℕ)
    (C e₀ e₁ : OpenPartialHomeomorph X (Fin n → ℂ)) (x : X)
    (hxC : x ∈ C.source) (hx₀ : x ∈ e₀.source)
    (hf : AnalyticAt ℂ (fun v => e₁ (C.symm v)) (C x))
    (hi : AnalyticAt ℂ (fun v => C (e₀.symm v)) (e₀ x)) :
    AnalyticAt ℂ (fun v => e₁ (e₀.symm v)) (e₀ x) := by
  have hc : C (e₀.symm (e₀ x)) = C x := by rw [e₀.left_inv hx₀]
  have ha := hf.comp_of_eq hi hc
  apply ha.congr
  have hn : ∀ᶠ v in 𝓝 (e₀ x), e₀.symm v ∈ C.source := by
    have ht := (e₀.continuousAt_symm (e₀.map_source hx₀)).tendsto
    rw [e₀.left_inv hx₀] at ht
    exact ht (C.open_source.mem_nhds hxC)
  filter_upwards [hn] with v hv
  change e₁ (C.symm (C (e₀.symm v))) = e₁ (e₀.symm v)
  rw [C.left_inv hv]

#print axioms s2e_analytic_chart_transition
end HodgeLean.Foundations.Program
