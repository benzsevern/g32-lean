import HodgeLean.Foundations.BundleThom.ProductBaseMapHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativePairHelpers

/-! # Actual relative product domains in base coordinates

Arbitrary base subsets carry their inherited topology and exact normal complement.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The product pair over a supplied base subset is the actual relative pair on its base-preimage domain.
Source: Hatcher, Algebraic Topology, §2.1, relative product coordinates. -/
def i1_productSubsetPairIso (B : Type) [TopologicalSpace B] (k : ℕ) (S : Set B) :
    i1_productNormalPair S k ≅
      i1_subsetRelativePair (TopCat.of (B × (Fin k → ℂ))) {p | p.2 ≠ 0}
        (Prod.fst ⁻¹' S) := by
  let e : (S × (Fin k → ℂ)) ≃ₜ {p : B × (Fin k → ℂ) // p.1 ∈ S} := {
    toFun := fun p => ⟨(p.1.1, p.2), p.1.2⟩
    invFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun :=
      (continuous_fst.subtype_val.prodMk continuous_snd).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd }
  exact TopPair.isoOfSubset e (fun _ => Iff.rfl)

/-- Product subset coordinates commute with the actual relative-domain inclusion.
Source: Hatcher, Algebraic Topology, §2.1, naturality of product coordinates. -/
theorem i1_productSubsetPairIso_comp_inclusion (B : Type) [TopologicalSpace B]
    (k : ℕ) (S : Set B) :
    (i1_productSubsetPairIso B k S).hom ≫
      i1_subsetRelativePairInclusion (TopCat.of (B × (Fin k → ℂ)))
        {p | p.2 ≠ 0} (Prod.fst ⁻¹' S) =
      i1_productBaseMap k (Subtype.val : S → B) continuous_subtype_val := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

end HodgeLean.Foundations.BundleThom
