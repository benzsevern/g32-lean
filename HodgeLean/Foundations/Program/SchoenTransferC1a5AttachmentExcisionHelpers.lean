import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentCoverHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5SubspaceExcisionHelpers

/-! Actual open-cover relative comparisons on both sides of an attachment.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The cell neighborhood together with the unattached cell part covers the whole cell piece.
Source: Hatcher §2.1, Theorem 2.20, the neighborhood/complement cover. -/
lemma c1a5_cell_collar_cover {A U C : TopCat.{0}} (j : A ⟶ U) (k : U ⟶ C) :
    Set.range k ∪ (Set.range (j ≫ k))ᶜ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Set.range (j ≫ k)
  · obtain ⟨a, rfl⟩ := hx
    exact Or.inl ⟨j a, rfl⟩
  · exact Or.inr hx

/-- Open-cover relative excision on the cell side of a boundary collar factorization.
Source: Hatcher §2.1, Theorem 2.20, integral small-chain subdivision. -/
lemma c1a5_cell_collar_relative_excision {A U C : TopCat.{0}}
    (j : A ⟶ U) (k : U ⟶ C) (hk : Topology.IsOpenEmbedding k)
    (hc : IsClosed (Set.range (j ≫ k))) :
    let N := Set.range k
    let V := (Set.range (j ≫ k))ᶜ
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (c1a5_subset_map C (Set.inter_subset_right : N ∩ V ⊆ V)))
      (TopCat.toSSet.map (topologicalSubsetInclusion C N))
      (TopCat.toSSet.map (c1a5_subset_map C (Set.inter_subset_left : N ∩ V ⊆ N)))
      (TopCat.toSSet.map (topologicalSubsetInclusion C V)) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl)) := by
  dsimp only
  exact c1a5_subspace_open_cover_excision C _ _ hk.isOpen_range hc.isOpen_compl
    (c1a5_cell_collar_cover j k)

/-- Open-cover relative excision on the attached side of an actual collar pushout.
Source: Hatcher §2.1, Theorem 2.20; the actual attachment neighborhood/complement cover. -/
lemma c1a5_attached_collar_relative_excision {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hk : Topology.IsOpenEmbedding k)
    (hl : Function.Injective (j ≫ k)) (hc : IsClosed (Set.range (j ≫ k))) :
    let N := Set.range (c1a5_attached_collar_map sq)
    let V := (Set.range r)ᶜ
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (c1a5_subset_map D (Set.inter_subset_right : N ∩ V ⊆ V)))
      (TopCat.toSSet.map (topologicalSubsetInclusion D N))
      (TopCat.toSSet.map (c1a5_subset_map D (Set.inter_subset_left : N ∩ V ⊆ N)))
      (TopCat.toSSet.map (topologicalSubsetInclusion D V)) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl)) := by
  dsimp only
  exact c1a5_subspace_open_cover_excision D _ _
    (c1a5_attached_collar_isOpenEmbedding sq hk).isOpen_range
    (c1a5_pushout_left_range_isClosed sq hl hc).isOpen_compl
    (c1a5_attached_collar_cover sq)

end HodgeLean.Foundations.Program
