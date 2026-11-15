import HodgeLean.Foundations.Program.SchoenCyclePairedClusters

/-! # Effective divisors recovered from disjoint curve charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Exact multiplicities in disjoint curve charts recover an entire effective divisor. -/
theorem residual_effective_divisor_eq_disjoint_chart_tuples
    [T2Space C] [CompactSpace C] [ConnectedSpace C] {ι : Type} [Fintype ι]
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p)
    (p : ι → C) (r : ι → ℝ) (d : ι → ℕ) (z : (i : ι) → Fin (d i) → ℂ)
    (ht : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w ∈
        (extChartAt 𝓘(ℂ, E) (p i)).target)
    (hz : ∀ i j, z i j ∈ Metric.ball (0 : ℂ) (r i))
    (hm : ∀ i w, w ∈ Metric.ball (0 : ℂ) (r i) →
      (Fintype.card {j : Fin (d i) // z i j = w} : ℤ) = D
        ((extChartAt 𝓘(ℂ, E) (p i)).symm
          (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)))
    (hd : b4c_deg (D) = ((∑ i, d i : ℕ) : ℤ))
    (hdis : Pairwise (fun i j => Disjoint
      ((fun w => (extChartAt 𝓘(ℂ, E) (p i)).symm
        (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r i))
      ((fun w => (extChartAt 𝓘(ℂ, E) (p j)).symm
        (extChartAt 𝓘(ℂ, E) (p j) (p j) + b4cov_lineEquiv hE w)) '' Metric.ball 0 (r j)))) :
    D = ∑ i, ∑ j, Finsupp.single
      ((extChartAt 𝓘(ℂ, E) (p i)).symm
        (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE (z i j))) (1 : ℤ) := by
  classical
  let g := fun i w => (extChartAt 𝓘(ℂ, E) (p i)).symm
    (extChartAt 𝓘(ℂ, E) (p i) (p i) + b4cov_lineEquiv hE w)
  have hsub (i : ι) : ↑(∑ j, Finsupp.single (g i (z i j)) (1 : ℤ)).support ⊆
      g i '' Metric.ball 0 (r i) := by
    intro x hx
    by_contra hn
    have hne : ∀ j, g i (z i j) ≠ x := fun j he => hn ⟨z i j, hz i j, he⟩
    have hzero : (∑ j, Finsupp.single (g i (z i j)) (1 : ℤ)) x = 0 := by
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
      exact Finset.sum_eq_zero (fun j _ => ite_eq_right (hne j))
    exact (Finsupp.mem_support_iff.mp hx) hzero
  apply s2e_effectiveDivisor_eq_cluster_sum _ hD
    d hd (fun i j => g i (z i j))
  · intro i
    apply s2e_tuple_divisor_le_of_injective_coordinates D hD (Metric.ball (0 : ℂ) (r i))
      (g i) ?_ (z i) (hz i)
    · intro w hw
      exact le_of_eq (hm i w hw)
    · intro u hu v hv huv
      have he := (extChartAt 𝓘(ℂ, E) (p i)).symm.injOn (ht i u hu) (ht i v hv) huv
      exact (b4cov_lineEquiv hE).injective (add_left_cancel he)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdis hij) (hsub i hx) (hsub j hy)

#print axioms residual_effective_divisor_eq_disjoint_chart_tuples
end HodgeLean.Foundations.Program.G32Native
