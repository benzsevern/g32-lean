import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # Actual local homology through embeddings with neighborhood image -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Topology TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Excision transports actual point-complement homology through an embedding whose image is a neighborhood at that point.
Source: Hatcher, Algebraic Topology, section 2.2, point excision.
HC no distance; AV milestone no distance. -/
def properCycle_neighborhood_embedding_local_homology_iso
    (X Y : TopCat.{0}) [T1Space X] [T1Space Y] (f : X → Y) (hf : IsEmbedding f)
    (x : X) (hnb : Set.range f ∈ 𝓝 (f x)) (n : ℕ) :
    orientationGroup X n x ≅ orientationGroup Y n (f x) := by
  let V : Opens Y := ⟨interior (Set.range f), isOpen_interior⟩
  have hxV : f x ∈ V := mem_interior_iff_mem_nhds.mpr hnb
  let U : Opens X := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  let w : U := ⟨x, hxV⟩
  let e : U ≃ₜ V := hf.homeomorphOfSubsetRange (show (V : Set Y) ⊆ Set.range f from interior_subset)
  exact (properCycle_open_local_homology_iso X U w n).symm ≪≫
    properCycle_local_homology_homeomorph_iso (X := TopCat.of U) (Y := TopCat.of V) e w n ≪≫
    properCycle_open_local_homology_iso Y V (e w) n

/-- The same actual local comparison restricts to any retained geometric mark, using only a neighborhood in the ambient image.
Source: Hatcher, Algebraic Topology, section 2.2, excision and restriction to subspaces.
HC no distance; AV milestone no distance. -/
def properCycle_marked_embedding_local_homology_iso
    (X Y : TopCat.{0}) [T1Space X] [T1Space Y] (f : X → Y) (hf : IsEmbedding f)
    (T : Set X) (S : Set Y) (hmark : ∀ z, f z ∈ S ↔ z ∈ T)
    (x : T) (hnb : Set.range f ∈ 𝓝 (f x.val)) (n : ℕ) :
    orientationGroup (TopCat.of T) n x ≅
      orientationGroup (TopCat.of S) n ⟨f x.val, (hmark x.val).mpr x.property⟩ := by
  let g : T → S := fun z => ⟨f z.val, (hmark z.val).mpr z.property⟩
  have hg : IsEmbedding g := (hf.comp IsEmbedding.subtypeVal).codRestrict S _
  have hrange : Set.range g = Subtype.val ⁻¹' Set.range f := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, rfl⟩
    · rintro ⟨z, hzy⟩
      have hz : z ∈ T := (hmark z).mp (hzy.symm ▸ y.property)
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hng : Set.range g ∈ 𝓝 (g x) := by
    rw [hrange]
    exact continuous_subtype_val.tendsto (g x) hnb
  exact properCycle_neighborhood_embedding_local_homology_iso
    (TopCat.of T) (TopCat.of S) g hg x hng n

end HodgeLean.Foundations.QuotientDuality
