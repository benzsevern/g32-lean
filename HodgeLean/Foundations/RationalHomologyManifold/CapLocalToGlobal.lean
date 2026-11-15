import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleRepresentatives
import HodgeLean.Foundations.RationalHomologyManifold.FixedCapFinalNormalization

/-! The local-to-global step for the concrete fixed-cycle cap morphism.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Local homology concentration makes fixed-cycle cap an isomorphism on homology.
Source: Bredon, Sheaf Theory, second edition, V.9–10, V.16 and VI.12.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_fixedCycleCap_isIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (p q : ℕ)
    (o : LocalRationalOrientation X ((p + 1) + (q + 1)))
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0)
    (hlocal : localization X ((p + 1) + (q + 1))
      (((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
        (fixedTotalCycle X p q z hz)) = o.generator) :
    IsIso (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)) := by
  exact fixedCapWindow_homologyMap_isIso_of_fixedTotalCycle X t p q o z hz hlocal

#print axioms finiteTriangulation_fixedCycleCap_isIso
/-- Cycle representatives and the standard cochain comparison reduce positive cap to its concrete homology morphism.
Source: Hatcher, Algebraic Topology, section 3.3, cap on cycle representatives.
HC no distance; AV milestone no distance.
-/
theorem cap_positive (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (p q : ℕ)
    (o : LocalRationalOrientation X ((p + 1) + (q + 1)))
    (c : Homology ℚ X ((p + 1) + (q + 1)))
    (hc : localization X ((p + 1) + (q + 1)) c = o.generator) :
    Function.Bijective (localTraceCap X (p + 1) (q + 1) c) := by
  obtain ⟨z, hz, hclass⟩ := exists_fixedTotalCycle X p q c
  have hlocal : localization X ((p + 1) + (q + 1))
      (((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
        (fixedTotalCycle X p q z hz)) = o.generator := by
    rw [hclass]
    exact hc
  letI := finiteTriangulation_fixedCycleCap_isIso X t p q o z hz hlocal
  have hb := ConcreteCategory.bijective_of_isIso
    (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz))
  have heq : (fun a : Cohomology ℚ X (p + 1) =>
      (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)).hom
        ((cochainCohomologyEquiv ℚ X (p + 1)).symm a)) =
      localTraceCap X (p + 1) (q + 1) c := by
    funext a
    have h := fixedCycleCapHom_localTraceCap X p q z hz a
    simpa only [hclass] using h
  rw [← heq]
  exact hb.comp (cochainCohomologyEquiv ℚ X (p + 1)).symm.bijective

#print axioms cap_positive
end HodgeLean.Foundations.RationalHomologyManifold
