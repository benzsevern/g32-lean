import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOpenExcision

/-! # Small singular covers restricted to an actual subspace -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting small singular simplices to a subspace restricts each actual cover member.
Source: Hatcher, Algebraic Topology, section 2.2, small singular simplices.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_subspace_preimage
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X) :
    (coverSmallSingularSubcomplex X U).preimage
        (TopCat.toSSet.map (topologicalSubsetInclusion X S)) =
      coverSmallSingularSubcomplex (TopCat.of S) (fun i => Subtype.val ⁻¹' U i) := by
  ext n σ
  simp only [SSet.Subcomplex.preimage_obj, Set.mem_preimage,
    mem_coverSmallSingularSubcomplex_iff]
  change (∃ i, (TopCat.toSSet.map (topologicalSubsetInclusion X S)).app n σ ∈
      (subsetSingularSubcomplex X (U i)).obj n) ↔
    ∃ i, σ ∈ (subsetSingularSubcomplex (TopCat.of S) (Subtype.val ⁻¹' U i)).obj n
  simp only [mem_subsetSingularSubcomplex_iff]
  rfl

/-- An actual cover contained in a subspace is recovered by taking the image of its restricted small singular complex.
Source: Hatcher, Algebraic Topology, section 2.2, small singular simplices.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_subspace_image
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUS : ∀ i, U i ⊆ S) :
    (coverSmallSingularSubcomplex (TopCat.of S) (fun i => Subtype.val ⁻¹' U i)).image
        (TopCat.toSSet.map (topologicalSubsetInclusion X S)) =
      coverSmallSingularSubcomplex X U := by
  rw [← properCycle_small_cover_subspace_preimage]
  apply le_antisymm (SSet.Subcomplex.image_preimage_le _ _)
  intro n σ hσ
  have hS : σ ∈ (subsetSingularSubcomplex X S).obj n := by
    obtain ⟨i, hi⟩ := (mem_coverSmallSingularSubcomplex_iff X U σ).mp hσ
    exact (mem_subsetSingularSubcomplex_iff X S σ).mpr (fun t =>
      hUS i ((mem_subsetSingularSubcomplex_iff X (U i) σ).mp hi t))
  obtain ⟨τ, hτ⟩ := hS
  exact ⟨τ, by change (TopCat.toSSet.map (topologicalSubsetInclusion X S)).app n τ ∈ (coverSmallSingularSubcomplex X U).obj n; rwa [hτ], hτ⟩

/-- The actual small singular cover of a subspace is isomorphic to its ambient image, through the literal subspace inclusion.
Source: Hatcher, Algebraic Topology, section 2.2, small singular simplices.
HC no distance; AV milestone no distance. -/
def properCycle_small_cover_subspace_iso
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUS : ∀ i, U i ⊆ S) :
    (coverSmallSingularSubcomplex (TopCat.of S) (fun i => Subtype.val ⁻¹' U i) : SSet) ≅
      coverSmallSingularSubcomplex X U := by
  let f := TopCat.toSSet.map (topologicalSubsetInclusion X S)
  let A := coverSmallSingularSubcomplex (TopCat.of S) (fun i => Subtype.val ⁻¹' U i)
  letI : Mono f := subsetSingularMap_mono X S
  letI : Mono (A.toImage f) := mono_of_mono_fac (SSet.Subcomplex.toImage_ι A f)
  letI : IsIso (A.toImage f) := isIso_of_mono_of_epi _
  exact asIso (A.toImage f) ≪≫
    SSet.Subcomplex.eqToIso (properCycle_small_cover_subspace_image X U S hUS)

/-- The restricted-cover isomorphism retains the original inclusion of every actual singular simplex.
Source: Hatcher, Algebraic Topology, section 2.2, small singular simplices.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_subspace_iso_inclusion
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUS : ∀ i, U i ⊆ S) :
    (properCycle_small_cover_subspace_iso X U S hUS).hom ≫
        (coverSmallSingularSubcomplex X U).ι =
      (coverSmallSingularSubcomplex (TopCat.of S) (fun i => Subtype.val ⁻¹' U i)).ι ≫
        TopCat.toSSet.map (topologicalSubsetInclusion X S) := by
  rfl

/-- Every simplex small for a cover contained in a subspace belongs to the actual singular subcomplex of that subspace.
Source: Hatcher, Algebraic Topology, section 2.2, small singular simplices.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_le_subset
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUS : ∀ i, U i ⊆ S) :
    coverSmallSingularSubcomplex X U ≤ subsetSingularSubcomplex X S := by
  rw [← properCycle_small_cover_subspace_image X U S hUS]
  exact SSet.Subcomplex.image_le_range _ _

end HodgeLean.Foundations.QuotientDuality
