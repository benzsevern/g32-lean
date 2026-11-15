import HodgeLean.Foundations.RationalHomologyManifold.CapTargetGlobalWindowQuasiIso
import HodgeLean.Foundations.RationalHomologyManifold.AbsoluteSupportedGlobalComparison

/-! Actual singular chains compared to the global bounded cap window.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Project the original singular-chain window to actual global supported chains, then retain the specified bounded cap signs and initial quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
def singularCapTargetWindowComparison (X : TopCat.{0}) (p q : ℕ) :
    (((SingularChainComplex ℚ X).sc' (q + 2) (q + 1) q).map
      (forget₂ (ModuleCat ℚ) AddCommGrpCat)) ⟶
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (capTargetComplex X (p + q + 2))).sc' p (p + 1) (p + 2)) :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat (.down ℕ) (q + 2) (q + 1) q).map
      (absoluteSubdivisionGlobalComparison X) ≫
    ((subdivisionGlobalSectionsFunctor X).mapShortComplex).map (capTargetWindowComparison X p q)

#print axioms singularCapTargetWindowComparison
/-- The actual singular-to-global bounded cap-window comparison is a quasi-isomorphism with its original relative projection and adjacent signs.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual global supported-chain comparison and the boundary quotient.
HC no distance; AV milestone no distance.
-/
theorem singularCapTargetWindowComparison_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q + 2)) :
    ShortComplex.QuasiIso (singularCapTargetWindowComparison X p q) := by
  let f := absoluteSubdivisionGlobalComparison X
  letI := absoluteSubdivisionGlobalComparison_quasiIso X
  haveI : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (.down ℕ) (q + 2) (q + 1) q).map f) :=
    (quasiIsoAt_iff' f (q + 2) (q + 1) q (ChainComplex.prev ℕ (q + 1))
      (ChainComplex.next_nat_succ q)).mp inferInstance
  letI := capTargetWindowComparison_global_quasiIso X t p q o
  exact ShortComplex.quasiIso_comp _ _

#print axioms singularCapTargetWindowComparison_quasiIso
/-- The actual singular-to-cap comparison retains the ordinary stage-zero chain projection in its middle component.
Source: Bredon, Sheaf Theory, second edition, VI.12; normalization of the actual singular cap window.
HC no distance; AV milestone no distance.
-/
theorem singularCapTargetWindowComparison_middle (X : TopCat.{0}) (p q : ℕ) :
    (singularCapTargetWindowComparison X p q).τ₂ =
      subdivisionAmbientSectionMap X (q + 1) ⊤ 0 ≫
        (subdivisionGlobalSectionsFunctor X).map
          (capTargetTermIso X (p + q + 2) (p + 1) (q + 1) (by omega) (by omega)).inv := by
  change (absoluteSubdivisionGlobalComparison X).f (q + 1) ≫
      (subdivisionGlobalSectionsFunctor X).map (capTargetWindowComparison X p q).τ₂ = _
  rw [absoluteSubdivisionGlobalComparison_component, capTargetWindowComparison_middle]

#print axioms singularCapTargetWindowComparison_middle
end HodgeLean.Foundations.RationalHomologyManifold
