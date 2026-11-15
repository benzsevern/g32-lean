import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapDescentNormalization
import HodgeLean.Foundations.RationalHomologyManifold.AmbientUnitRestriction

/-! Actual unit normalization of the descended fixed-cycle cap map.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual fixed-cycle cap descends with its original local cup-unit value retained literally in degree zero.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedCycleCap_descent_unit (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    [∀ p, Injective (I.X p)] (j : capTargetComplex X N ⟶ I) :
    ∃ d : singularCochainSheafComplex ℚ X ⟶ I,
      Nonempty (Homotopy (ambientFixedCycleCapComplexHom X N z hz ≫ j)
        (ambientCochainSheafRestriction X ≫ d)) ∧
      constantsToSingularCochainZeroSheaf ℚ X ≫ d.f 0 =
        ambientConstantsToZeroSheaf X ≫ ambientCapTargetComponent X N z 0 ≫ j.f 0 := by
  obtain ⟨d, h, hd⟩ := exists_fixedCycleCap_descent_initial X N z hz I j
  refine ⟨d, h, ?_⟩
  have hu := hd _ (ambientConstantsToZeroSheaf X) (ambientConstantsToZeroSheaf_coboundary X)
  rw [← ambientConstantsToZeroSheaf_restriction X, Category.assoc]
  exact hu.symm

#print axioms exists_fixedCycleCap_descent_unit
end HodgeLean.Foundations.RationalHomologyManifold
