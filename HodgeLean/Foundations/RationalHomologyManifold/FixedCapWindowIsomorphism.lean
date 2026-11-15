import HodgeLean.Foundations.RationalHomologyManifold.FixedCapGlobalWindowSquare
import HodgeLean.Foundations.RationalHomologyManifold.ShortComplexMiddleComparison

/-! Actual fixed cap isomorphism from the normalized global window comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original literal fixed-cycle cap short-complex map induces an isomorphism from the actual normalized local orientation and finite triangulation.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem fixedCapWindow_homologyMap_isIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q + 2))
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0)
    (hc : localization X (p + q + 2)
      (((SingularChainComplex ℚ X).sc (p + q + 2)).moduleCatHomologyClass
        (scalarAmbientCycle X (p + q + 1) z hz)) = o.generator) :
    IsIso (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)) := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let f := F.mapShortComplex.map (fixedCycleCapHom X p q z hz)
  let β := singularCapTargetStandardWindowComparison X p q
  let hz' := fixedCapCycle_all_differentials X p q z hz
  let α := globalFixedCycleCapWindow X p q z hz'
  letI : ShortComplex.QuasiIso α := globalFixedCycleCapWindow_quasiIso X t p q o z hz' hc
  letI : ShortComplex.QuasiIso β := singularCapTargetStandardWindowComparison_quasiIso X t p q o
  have he : ShortComplex.homologyMap (f ≫ β) = ShortComplex.homologyMap α :=
    shortComplex_homologyMap_eq_of_middle (f ≫ β) α (fixedCycleCapHom_global_window_middle X p q z hz)
  haveI : ShortComplex.QuasiIso (f ≫ β) := by
    rw [ShortComplex.quasiIso_iff, he]
    infer_instance
  have hf : ShortComplex.QuasiIso f := ShortComplex.quasiIso_of_comp_right f β
  letI := rationalShortComplex_quasiIso_of_forget (fixedCycleCapHom X p q z hz) hf
  infer_instance

#print axioms fixedCapWindow_homologyMap_isIso
end HodgeLean.Foundations.RationalHomologyManifold
