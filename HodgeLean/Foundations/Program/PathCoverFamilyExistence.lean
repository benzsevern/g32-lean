import HodgeLean.Foundations.Program.PathCoverFamilyDefs

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_group_nielsen (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) : b4_Nielsen g := by
  constructor
  · apply Subtype.val_injective
    have h := hg.2.1
    change b4b_toMatrix (List.ofFn g).prod = b4b_toMatrix 1
    rw [map_list_prod, map_one, List.map_ofFn]
    exact h
  · apply top_unique
    intro a ha
    have hm : b4b_toMatrix a ∈ Submonoid.closure (Set.range (fun i ↦ b4b_toMatrix (g i))) := by
      rw [hg.2.2]
      exact a.property
    have hx : ∃ b ∈ Subgroup.closure (Set.range g), b4b_toMatrix b = b4b_toMatrix a := by
      generalize hM : b4b_toMatrix a = M at hm ⊢
      clear hM
      induction hm using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
      | one => exact ⟨1, Subgroup.one_mem _, map_one _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨u, hu, heu⟩ := hx
        obtain ⟨v, hv, hev⟩ := hy
        exact ⟨u * v, Subgroup.mul_mem _ hu hv, by rw [map_mul, heu, hev]⟩
    obtain ⟨b, hb, he⟩ := hx
    have hba : b = a := Subtype.val_injective he
    exact hba ▸ hb

end HodgeLean.Foundations.Program
