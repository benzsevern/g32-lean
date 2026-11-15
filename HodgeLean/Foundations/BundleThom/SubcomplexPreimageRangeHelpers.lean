import HodgeLean.Foundations.BundleThom.RelativeChainQuasiIsoHelpers

/-! # Actual preimage and range comparisons for singular subcomplexes

A monic simplicial map identifies its preimage subcomplex with the actual intersection of the target subcomplex and its range.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual preimage subcomplex of a monic simplicial map is isomorphic to its target intersection with the map's range.
Source: Hatcher, Algebraic Topology, §2.2, subspace and small-chain identifications. -/
def i1_subcomplexPreimageRangeIso {X Y : SSet} (f : X ⟶ Y) [Mono f] (A : Y.Subcomplex) :
    (A.preimage f : SSet) ≅ ((A ⊓ SSet.Subcomplex.range f : Y.Subcomplex) : SSet) := by
  let g : (A.preimage f : SSet) ⟶ ((A ⊓ SSet.Subcomplex.range f : Y.Subcomplex) : SSet) := {
    app := fun n => TypeCat.ofHom (fun x : (A.preimage f).obj n =>
      (⟨f.app n x.1, x.2, ⟨x.1, rfl⟩⟩ : (A ⊓ SSet.Subcomplex.range f).obj n))
    naturality := by
      intro n m p
      ext x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (f.naturality p) x.1 }
  have hg (n : SimplexCategoryᵒᵖ) : Function.Bijective (g.app n) := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply (CategoryTheory.mono_iff_injective (f.app n)).mp inferInstance
      exact congrArg Subtype.val hxy
    · rintro ⟨y, hy, ⟨x, hx⟩⟩
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change f.app n x ∈ A.obj n
        rw [hx]
        exact hy
      · apply Subtype.ext
        exact hx
  exact NatIso.ofComponents (fun n => (Equiv.ofBijective (g.app n) (hg n)).toIso)
    (fun p => g.naturality p)

/-- The actual preimage–range isomorphism retains the ambient simplicial map after inclusion.
Source: Hatcher, Algebraic Topology, §2.2, naturality of subspace identifications. -/
theorem i1_subcomplexPreimageRangeIso_hom_comp {X Y : SSet} (f : X ⟶ Y) [Mono f]
    (A : Y.Subcomplex) :
    (i1_subcomplexPreimageRangeIso f A).hom ≫
      SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ SSet.Subcomplex.range f ≤ A) ≫ A.ι =
      (A.preimage f).ι ≫ f := by
  rfl

end HodgeLean.Foundations.BundleThom
