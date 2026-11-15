import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapUnitDescent
import HodgeLean.Foundations.RationalHomologyManifold.AmbientUnitComplex

/-! Actual unit-augmented descent of fixed-cycle cap.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual fixed-cycle cap descends through local singular cochains with a commuting square of the original cup-unit augmentations, as morphisms of complexes.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedCycleCap_descent_augmented (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    [∀ p, Injective (I.X p)] (j : capTargetComplex X N ⟶ I) :
    ∃ d : singularCochainSheafComplex ℚ X ⟶ I,
      Nonempty (Homotopy (ambientFixedCycleCapComplexHom X N z hz ≫ j)
        (ambientCochainSheafRestriction X ≫ d)) ∧
      constantsToSingularCochainSheafComplex ℚ X ≫ d =
        ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X N z hz ≫ j := by
  obtain ⟨d, h, hd⟩ := exists_fixedCycleCap_descent_unit X N z hz I j
  refine ⟨d, h, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext p
  cases p with
  | zero =>
      simp only [HomologicalComplex.comp_f, ambientCupUnitComplexHom_zero,
        constantsToSingularCochainSheafComplex,
        CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      exact hd
  | succ p =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ (p + 1) (by omega)).eq_of_src _ _

#print axioms exists_fixedCycleCap_descent_augmented
end HodgeLean.Foundations.RationalHomologyManifold
