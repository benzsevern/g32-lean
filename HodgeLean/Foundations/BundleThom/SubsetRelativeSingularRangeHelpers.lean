import HodgeLean.Foundations.BundleThom.SubsetRelativePairHelpers

/-! # Actual singular range coordinates for the relative subspace of a domain

The double subspace singular complex maps isomorphically to the intersection of the two supplied ambient ranges.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable (X : TopCat) (Z U : Set X)
private local instance (T : TopCat) (S : Set T) : Mono (topologicalSubsetInclusion T S) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective
private local instance (T : TopCat) (S : Set T) :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion T S)) := by apply Functor.map_mono

/-- The actual singular relative-subspace map of a supplied domain identifies it with the ambient range intersection.
Source: Hatcher, Algebraic Topology, §2.2, subspace chain identifications. -/
def i1_subsetRelativeSingularRangeIso :
    TopCat.toSSet.obj (i1_subsetRelativePair X Z U).snd ≅
      ((i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X Z :
        (TopCat.toSSet.obj X).Subcomplex) : SSet) := by
  let f := TopCat.toSSet.map (topologicalSubsetInclusion X U)
  let j := TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.of U) {u : U | u.1 ∈ Z})
  let g : TopCat.toSSet.obj (i1_subsetRelativePair X Z U).snd ⟶
      ((i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X Z :
        (TopCat.toSSet.obj X).Subcomplex) : SSet) := {
    app := fun n => TypeCat.ofHom (fun τ => ⟨f.app n (j.app n τ), ⟨j.app n τ, rfl⟩, by
      apply (i1_mem_singularSubsetRange_iff X Z _).mpr
      intro t
      change (((i1_subsetRelativePair X Z U).snd.toSSetObjEquiv n τ t).1).1 ∈ Z
      exact ((i1_subsetRelativePair X Z U).snd.toSSetObjEquiv n τ t).2⟩)
    naturality := by
      intro n m p
      ext τ
      apply Subtype.ext
      exact ConcreteCategory.congr_hom ((j ≫ f).naturality p) τ }
  have hg (n : SimplexCategoryᵒᵖ) : Function.Bijective (g.app n) := by
    constructor
    · intro τ σ hτσ
      apply (CategoryTheory.mono_iff_injective ((j ≫ f).app n)).mp inferInstance
      exact congrArg Subtype.val hτσ
    · rintro ⟨y, hyU, hyZ⟩
      obtain ⟨σ, hσ⟩ := hyU
      have hσZ : σ ∈ (i1_singularSubsetRange (TopCat.of U) {u : U | u.1 ∈ Z}).obj n := by
        apply (i1_mem_singularSubsetRange_iff (TopCat.of U) _ σ).mpr
        intro t
        have hy := (i1_mem_singularSubsetRange_iff X Z y).mp hyZ t
        rw [← hσ] at hy
        exact hy
      obtain ⟨τ, hτ⟩ := hσZ
      refine ⟨τ, ?_⟩
      apply Subtype.ext
      change f.app n (j.app n τ) = y
      rw [hτ, hσ]
  exact NatIso.ofComponents (fun n => (Equiv.ofBijective (g.app n) (hg n)).toIso)
    (fun p => g.naturality p)

end HodgeLean.Foundations.BundleThom
