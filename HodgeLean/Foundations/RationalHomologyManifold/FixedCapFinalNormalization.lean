import HodgeLean.Foundations.RationalHomologyManifold.FixedCapWindowIsomorphism

/-! Actual fixed total-cycle normalization for the original cap window.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual cap-window isomorphism retains the specified local normalization of the original fixed total-cycle representative.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem fixedCapWindow_homologyMap_isIso_of_fixedTotalCycle (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (p q : ℕ)
    (o : LocalRationalOrientation X ((p + 1) + (q + 1)))
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0)
    (hc : localization X ((p + 1) + (q + 1))
      (((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
        (fixedTotalCycle X p q z hz)) = o.generator) :
    IsIso (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)) := by
  let hdeg : p + q + 2 = (p + 1) + (q + 1) := by omega
  let o' : LocalRationalOrientation X (p + q + 2) := hdeg.symm ▸ o
  have hc' := localization_cycle_degree_transport X (p + q + 2) ((p + 1) + (q + 1))
    hdeg o (scalarAmbientCycle X (p + q + 1) z hz) (fixedTotalCycle X p q z hz)
    (by rfl) hc
  exact fixedCapWindow_homologyMap_isIso X t p q o' z hz hc'

#print axioms fixedCapWindow_homologyMap_isIso_of_fixedTotalCycle
end HodgeLean.Foundations.RationalHomologyManifold
