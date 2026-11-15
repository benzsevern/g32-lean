import HodgeLean.Foundations.Curves.AbelTheorem.FiniteGenericPoint

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem dense_complement_of_finite_smooth_paths (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → ℝ → C)
    (hγ : ∀ i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ i)) :
    Dense (⋃ i, Set.range (γ i))ᶜ := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  let V := (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' U
  have hV : IsOpen V := (chartAt E x).continuousOn_symm.isOpen_inter_preimage
    (chartAt E x).open_target hU
  have hv : chartAt E x x ∈ V := by
    refine ⟨(chartAt E x).map_source (mem_chart_source E x), ?_⟩
    simpa only [Set.mem_preimage, (chartAt E x).left_inv (mem_chart_source E x)] using hx
  obtain ⟨v, hvV, hgen⟩ := exists_generic_point_for_finite_paths h γ hγ x 0 0 hV ⟨_, hv⟩
  refine ⟨(chartAt E x).symm v, hvV.2, ?_⟩
  intro hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨s, hs⟩ := hi
  apply (hgen i).1
  refine ⟨s, ?_, ?_⟩
  · rw [hs]
    exact (chartAt E x).map_target hvV.1
  · rw [hs, (chartAt E x).right_inv hvV.1]

end HodgeLean.Foundations.Curves.AbelTheorem
