import Mathlib.Analysis.Analytic.Constructions
import HodgeLean.Foundations.Program.SchoenCycleAnalyticChartTransition

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- An analytic change between two charts on one space transports a centered chart to a second space with the same marked base coordinates, retaining both analytic directions.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Gunning and Rossi, Analytic Functions of Several Complex Variables, Chapter I. -/
theorem s2e_analytic_chart_transport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (C : OpenPartialHomeomorph Y (Fin n → ℂ))
    (e₀ e₁ : OpenPartialHomeomorph X (Fin n → ℂ)) (x : X) (y : Y)
    (hx₀ : x ∈ e₀.source) (hx₁ : x ∈ e₁.source) (hy : y ∈ C.source)
    (hcoord : e₀ x = C y) (hzero : e₁ x = 0)
    (hf : AnalyticAt ℂ (fun v => e₁ (e₀.symm v)) (e₀ x))
    (hi : AnalyticAt ℂ (fun v => e₀ (e₁.symm v)) (e₁ x)) :
    ∃ e : OpenPartialHomeomorph Y (Fin n → ℂ),
      y ∈ e.source ∧ e y = 0 ∧
      AnalyticAt ℂ (fun v => e (C.symm (C y + v))) 0 ∧
      AnalyticAt ℂ (fun v => C (e.symm v)) 0 ∧
      ∀ q, e q = e₁ (e₀.symm (C q)) := by
  let e := C.trans (e₀.symm.trans e₁)
  have hbase : e₀.symm (C y) = x := by rw [← hcoord, e₀.left_inv hx₀]
  have he : y ∈ e.source := by
    change y ∈ C.source ∧ C y ∈ (e₀.symm.trans e₁).source
    refine ⟨hy, ?_⟩
    change C y ∈ e₀.target ∧ e₀.symm (C y) ∈ e₁.source
    exact ⟨hcoord ▸ e₀.map_source hx₀, hbase ▸ hx₁⟩
  have hezero : e y = 0 := by
    change e₁ (e₀.symm (C y)) = 0
    rw [hbase, hzero]
  refine ⟨e, he, hezero, ?_, ?_, fun q => rfl⟩
  · have ha : AnalyticAt ℂ (fun v => e₁ (e₀.symm (C y + v))) 0 := by
      rw [hcoord] at hf
      exact hf.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero _)
    apply ha.congr
    have hn : ∀ᶠ v in 𝓝 (0 : Fin n → ℂ), C y + v ∈ C.target := by
      exact (continuous_const.add continuous_id).continuousAt
        (by simpa only [Pi.add_apply, id_eq, add_zero] using C.open_target.mem_nhds (C.map_source hy))
    filter_upwards [hn] with v hv
    change e₁ (e₀.symm (C y + v)) = e₁ (e₀.symm (C (C.symm (C y + v))))
    rw [C.right_inv hv]
  · rw [hzero] at hi
    apply hi.congr
    have hval : e₀ (e₁.symm (0 : Fin n → ℂ)) = C y := by
      rw [← hzero, e₁.left_inv hx₁, hcoord]
    have hn : ∀ᶠ v in 𝓝 (0 : Fin n → ℂ), e₀ (e₁.symm v) ∈ C.target := by
      exact hi.continuousAt (by rw [hval]; exact C.open_target.mem_nhds (C.map_source hy))
    filter_upwards [hn] with v hv
    change e₀ (e₁.symm v) = C (C.symm (e₀ (e₁.symm v)))
    rw [C.right_inv hv]

#print axioms s2e_analytic_chart_transport
end HodgeLean.Foundations.Program
