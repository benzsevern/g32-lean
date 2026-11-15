import HodgeLean.Foundations.Program.CodifferentialDictionaryAtlasRamificationProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

theorem b66d_projection_branch_iff {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (p : b65z_fibre c D.C t) (j : Fin 13) :
    b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t p = b6_branch t.val j ↔
      D.atlas.f p.val.2 = b6_branch c j := by
  obtain ⟨E, hE⟩ := b6t_homeomorph c D.atlas.hb t.val t.property
  have hp : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t p =
      E (D.atlas.f p.val.2) := by
    rw [hE]
    simp only [b63d_projection, b6a_map, p.property]
  have hm : b6_branch t.val j = E (b6_branch c j) := by
    rw [hE, b6t_marks c D.atlas.hb t.val t.property]
  rw [hp, hm]
  exact E.injective.eq_iff

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option maxHeartbeats 400000 in
theorem b66d_branch_degree {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (j : Fin 13) :
    (∑ x ∈ (b66d_branchPoles D).filter (fun x => D.atlas.f x = b6_branch c j),
      D.atlas.n x) = 155520 := by
  let π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  let E := b6m_coordinate c D.C t
  let S := (b66d_branchPoles D).filter (fun x => D.atlas.f x = b6_branch c j)
  have hS : (S : Set D.C) = D.atlas.f ⁻¹' {b6_branch c j} := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      apply Finset.mem_filter.mpr
      refine ⟨?_, hx⟩
      simp only [b66d_branchPoles, Set.Finite.mem_toFinset, Set.mem_preimage]
      exact ⟨j, hx.symm⟩
  have hE : (π ⁻¹' {b6_branch t.val j}).BijOn E (D.atlas.f ⁻¹' {b6_branch c j}) := by
    refine ⟨?_, E.injective.injOn, ?_⟩
    · intro p hp
      exact (b66d_projection_branch_iff D t p j).mp hp
    · intro x hx
      refine ⟨E.symm x, ?_, E.apply_symm_apply x⟩
      apply (b66d_projection_branch_iff D t (E.symm x) j).mpr
      exact hx
  have hdegree : b4_fiberDegree ℂ ℂ π (b6_branch t.val j) = ∑ x ∈ S, D.atlas.n x := by
    rw [b4_fiberDegree]
    calc
      (∑ᶠ p ∈ π ⁻¹' {b6_branch t.val j}, b4_ramIndex ℂ ℂ π p) =
          ∑ᶠ x ∈ D.atlas.f ⁻¹' {b6_branch c j}, D.atlas.n x := by
        apply finsum_mem_eq_of_bijOn E hE
        intro p hp
        exact b66d_atlas_ramIndex D t p j ((b66d_projection_branch_iff D t p j).mp hp)
      _ = _ := by rw [← hS, finsum_mem_coe_finset]
  have hg := b4_fiberDegree_galois (by simp) (by simp) (D.hG t) π (D.hk t) (D.hgal t)
    (b6_branch t.val j)
  have hc : Nat.card b4b_Group = 155520 := by
    rw [← Fintype.card_eq_nat_card, b63l_card_group]
  exact hdegree.symm.trans (hg.trans hc)

end HodgeLean.Foundations.Program
