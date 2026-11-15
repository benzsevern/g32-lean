import HodgeLean.Foundations.Program.SchoenTransferC1a5CoverTransportHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentOverlapHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentExcisionHelpers

/-! Integral relative comparison for actual attachment neighborhoods.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A topological intersection can be regarded as the first subspace inside the second.
Source: the subspace topology and associativity of subtype formation. -/
def c1a5_intersection_subtype_homeomorph (X : TopCat.{0}) (U V : Set X) :
    (U ∩ V : Set X) ≃ₜ {x : V // x.val ∈ U} where
  toFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  invFun x := ⟨x.val.val, ⟨x.property, x.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

example (X : TopCat.{0}) (U V : Set X) := c1a5_intersection_subtype_homeomorph X U V

/-- The actual overlap homeomorphism in the unnested intersection subspaces.
Source: the attachment complement homeomorphism restricted to the actual collar overlaps. -/
def c1a5_attachment_intersection_homeomorph {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hl : Function.Injective (j ≫ k))
    (hc : IsClosed (Set.range (j ≫ k))) (hk : Function.Injective k) :
    (Set.range k ∩ (Set.range (j ≫ k))ᶜ : Set C) ≃ₜ
      (Set.range (c1a5_attached_collar_map sq) ∩ (Set.range r)ᶜ : Set D) :=
  (c1a5_intersection_subtype_homeomorph C _ _).trans
    ((c1a5_pushout_collar_overlap_homeomorph sq hl hc hk).trans
      (c1a5_intersection_subtype_homeomorph D _ _).symm)

example := @c1a5_attachment_intersection_homeomorph

/-- The literal cell map induces relative comparison after replacing both attaching subspaces
by their actual open neighborhood images.
Source: Hatcher §2.1, Theorem 2.20, the two neighborhood covers and complement homeomorphisms. -/
lemma c1a5_attachment_neighborhood_relative_comparison {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hk : Topology.IsOpenEmbedding k)
    (hl : Function.Injective (j ≫ k)) (hc : IsClosed (Set.range (j ≫ k))) :
    let N := Set.range k
    let N' := Set.range (c1a5_attached_collar_map sq)
    let hN : ∀ x ∈ N, b x ∈ N' := by
      intro x hx
      exact (Set.ext_iff.mp (c1a5_attached_collar_preimage sq hk.injective) x).mpr hx
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (topologicalSubsetInclusion C N))
      (TopCat.toSSet.map (topologicalSubsetInclusion D N'))
      (TopCat.toSSet.map (c1a5_map_subspace b N N' hN))
      (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl)) := by
  dsimp only
  let N := Set.range k
  let N' := Set.range (c1a5_attached_collar_map sq)
  let V := (Set.range (j ≫ k))ᶜ
  let V' := (Set.range r)ᶜ
  have hN : ∀ x ∈ N, b x ∈ N' := by
    intro x hx
    exact (Set.ext_iff.mp (c1a5_attached_collar_preimage sq hk.injective) x).mpr hx
  have hV : ∀ x ∈ V, b x ∈ V' := by
    intro x hx
    exact (c1a5_pushout_complement_map sq hl ⟨x, hx⟩).property
  apply c1a5_open_cover_relative_transport b N V N' V'
    hk.isOpen_range hc.isOpen_compl (c1a5_cell_collar_cover j k)
    (c1a5_attached_collar_isOpenEmbedding sq hk).isOpen_range
    (c1a5_pushout_left_range_isClosed sq hl hc).isOpen_compl
    (c1a5_attached_collar_cover sq) hN hV
  · have he : c1a5_map_subspace b (N ∩ V) (N' ∩ V')
        (fun x hx ↦ ⟨hN x hx.1, hV x hx.2⟩) =
        (TopCat.isoOfHomeo (c1a5_attachment_intersection_homeomorph sq hl hc hk.injective)).hom := by
      ext x
      rfl
    rw [he]
    infer_instance
  · have he : c1a5_map_subspace b V V' hV =
        (TopCat.isoOfHomeo (c1a5_pushout_complement_homeomorph sq hl hc)).hom := by
      ext x
      rfl
    rw [he]
    infer_instance

end HodgeLean.Foundations.Program
