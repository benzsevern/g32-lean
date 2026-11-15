import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadMapExcision

/-! # Original cap duality under actual maps of triads -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original triad cap bijectivity transports through actual bijective homology maps on its source and target, with the cohomology class pulled back by the literal first-pair map.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_cap_bijective_of_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) C) p)
    (hF : Function.Bijective (HomologicalComplex.homologyMap
      (properCycle_triad_relative_chain_map f A B C D hA hB) (p + q)).hom)
    (hG : Function.Bijective (relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)))
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y C D p q a)) :
    Function.Bijective (triadCapCohomologyLinear ℚ X A B p q
      (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) a)) := by
  constructor
  · intro x y hxy
    apply hF.1
    apply hc.1
    rw [← properCycle_triad_cap_naturality f A B C D hA hB p q a x,
      ← properCycle_triad_cap_naturality f A B C D hA hB p q a y, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hc.2 (relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB) y)
    obtain ⟨x, hx⟩ := hF.2 z
    refine ⟨x, hG.1 ?_⟩
    rw [properCycle_triad_cap_naturality, hx, hz]

end HodgeLean.Foundations.QuotientDuality
