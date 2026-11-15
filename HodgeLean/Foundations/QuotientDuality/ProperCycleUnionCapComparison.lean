import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapComparison

/-! # Original cap product through the actual union-relative excision pairing -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- For actual open triad subspaces, projecting the original cap class is the union-relative cap of the projected original fundamental class.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_union_relative_projection
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p)
    (c : Homology ℚ X (p + q)) :
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm
          (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (X := X) A) p a)) c) =
      unionRelativeTriadCapCohomologyLinear ℚ X A B p q
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) a
        ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (A ∪ B)) (p + q)).hom c) := by
  have hp : triadToUnionRelativeHomologyMap ℚ X A B (p + q)
      ((HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) (p + q)).hom c) =
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (A ∪ B)) (p + q)).hom c := by
    have hm := congrArg (fun f => HomologicalComplex.homologyMap f (p + q))
      (triadRelativeChainProjection_triadToUnionRelativeChainMap ℚ X A B)
    rw [HomologicalComplex.homologyMap_comp] at hm
    exact ConcreteCategory.congr_hom hm c
  have ht := unionRelativeTriadCapCohomologyLinear_on_comparison ℚ X A B p q
    (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) a
    ((HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) (p + q)).hom c)
  have hc := congrArg (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
    (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) a) hp
  exact (properCycle_cap_relative_projection_cohomology X A B p q a c).trans
    (ht.symm.trans hc)

end HodgeLean.Foundations.QuotientDuality
