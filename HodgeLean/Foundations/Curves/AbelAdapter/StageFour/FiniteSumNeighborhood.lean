import Mathlib.Topology.Algebra.Monoid

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Bourbaki, General Topology, chapter III, §1, continuity of finite sums. -/
theorem finite_sum_neighborhood {A ι : Type*} [AddCommMonoid A]
    [TopologicalSpace A] [ContinuousAdd A] [Fintype ι]
    (a : ι → A) (U : Set A) (hU : U ∈ 𝓝 (∑ i, a i)) :
    ∃ V : ι → Set A, (∀ i, V i ∈ 𝓝 (a i)) ∧
      ∀ b : ι → A, (∀ i, b i ∈ V i) → (∑ i, b i) ∈ U := by
  have hc : Continuous (fun b : ι → A ↦ ∑ i, b i) :=
    continuous_finsetSum Finset.univ (fun i _ ↦ continuous_apply i)
  have hp : (fun b : ι → A ↦ ∑ i, b i) ⁻¹' U ∈ 𝓝 a := hc.continuousAt hU
  rw [nhds_pi] at hp
  obtain ⟨I, _, V, hV, hsub⟩ := Filter.mem_pi.mp hp
  exact ⟨V, hV, fun b hb ↦ hsub (fun i _ ↦ hb i)⟩

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
