import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionSupportBaseUnit
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeCapNaturality

/-! # Original ordinary support-relative cap naturality
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal transport of intersection-support pairs through the specified complement-union identifications and actual ambient map.
Source: properCycle_support_complement_union_iso; AlgebraicTopology.Singular.TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
def properCycle_support_intersection_pair_map {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S T : Set X) (U V : Set Y) (hS : Set.MapsTo f Sᶜ Uᶜ) (hT : Set.MapsTo f Tᶜ Vᶜ) :
    TopPair.ofSubset (X := X) (S ∩ T)ᶜ ⟶ TopPair.ofSubset (X := Y) (U ∩ V)ᶜ :=
  (properCycle_support_complement_union_iso X S T).inv ≫
    TopPair.ofSubsetHom f (show Set.MapsTo f (Sᶜ ∪ Tᶜ) (Uᶜ ∪ Vᶜ) from
      fun _ h => h.elim (fun hs => Or.inl (hS hs)) (fun ht => Or.inr (hT ht))) ≫
    (properCycle_support_complement_union_iso Y U V).hom

/-- The original cap on ordinary intersection-support relative homology retains naturality through the literal ambient maps and specified original source excision.
Source: properCycle_union_relative_cap_naturality; properCycle_union_relative_support_cap_apply.
HC no distance; AV milestone no distance. -/
theorem properCycle_support_cap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S T : Set X) (U V : Set Y) (hA : Set.MapsTo f Sᶜ Uᶜ) (hB : Set.MapsTo f Tᶜ Vᶜ)
    (hS : IsClosed S) (hT : IsClosed T) (hU : IsClosed U) (hV : IsClosed V)
    (p q : ℕ) (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Uᶜ) p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) (S ∩ T)ᶜ) (p+q)) :
    relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
      ((properCycle_union_relative_support_cap X S T hS hT p q
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) a)).hom z) =
      (properCycle_union_relative_support_cap Y U V hU hV p q a).hom
        (relativeHomologyMap ℚ (p+q) (properCycle_support_intersection_pair_map f S T U V hA hB) z) := by
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (Sᶜ ∪ Tᶜ) (Uᶜ ∪ Vᶜ) from
    fun _ h => h.elim (fun hs => Or.inl (hA hs)) (fun ht => Or.inr (hB ht)))
  have hp : properCycle_support_intersection_pair_map f S T U V hA hB ≫
      (properCycle_support_complement_union_iso Y U V).inv =
      (properCycle_support_complement_union_iso X S T).inv ≫ fU := by
    dsimp only [properCycle_support_intersection_pair_map]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hz := congrArg (fun m => relativeHomologyMap ℚ (p+q) m z) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hz
  simp only [properCycle_union_relative_support_cap_apply]
  rw [hz]
  exact properCycle_union_relative_cap_naturality f Sᶜ Tᶜ Uᶜ Vᶜ hA hB
    hS.isOpen_compl hT.isOpen_compl hU.isOpen_compl hV.isOpen_compl p q a
    (relativeHomologyMap ℚ (p+q) (properCycle_support_complement_union_iso X S T).inv z)

end HodgeLean.Foundations.QuotientDuality
