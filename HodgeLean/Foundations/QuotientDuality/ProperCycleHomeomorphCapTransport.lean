import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportCoclass

/-! # Original relative cap duality through actual homeomorphisms -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original triad cap bijectivity transports through an actual homeomorphism preserving the specified two open subspaces, with the original class pulled back by its pair isomorphism.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, naturality of excision and cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_triad_cap_bijective
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (A B : Set X) (C D : Set Y)
    (hAC : ∀ x, e x ∈ C ↔ x ∈ A) (hBD : ∀ x, e x ∈ D ↔ x ∈ B)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (p q : ℕ) (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) C) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y C D p q a)) :
    Function.Bijective (triadCapCohomologyLinear ℚ X A B p q
      (relativeCohomologyMap ℚ p (TopPair.isoOfSubset e hAC).hom a)) := by
  let f : X ⟶ Y := TopCat.ofHom ⟨e, e.continuous⟩
  let hA : Set.MapsTo f A C := fun x h => (hAC x).mpr h
  let hB : Set.MapsTo f B D := fun x h => (hBD x).mpr h
  apply properCycle_triad_cap_bijective_of_map f A B C D hA hB p q a
  · apply properCycle_triad_homology_bijective_of_union f A B C D hA hB hAo hBo hCo hDo (p + q)
    let eU := TopPair.isoOfSubset (A := A ∪ B) (B := C ∪ D) e (fun x => or_congr (hAC x) (hBD x))
    letI : IsIso eU.hom := eU.isIso_hom
    change Function.Bijective (HomologicalComplex.homologyMap
      ((relativeChainFunctor ℚ).map eU.hom) (p + q)).hom
    exact ConcreteCategory.bijective_of_isIso _
  · let eB := TopPair.isoOfSubset e hBD
    letI : IsIso eB.hom := eB.isIso_hom
    change Function.Bijective (HomologicalComplex.homologyMap
      ((relativeChainFunctor ℚ).map eB.hom) q).hom
    exact ConcreteCategory.bijective_of_isIso _
  · exact hc

end HodgeLean.Foundations.QuotientDuality
