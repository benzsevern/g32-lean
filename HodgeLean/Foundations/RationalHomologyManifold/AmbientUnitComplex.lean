import HodgeLean.Foundations.RationalHomologyManifold.AmbientUnitRestriction

/-! The actual cup-unit augmentation into ambient cochains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Include the constant rational sheaf in the actual ambient cochain complex through its cup-unit cocycle.
Source: Hatcher, Algebraic Topology, section 3.2; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def ambientCupUnitComplexHom (X : TopCat.{0}) :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} X)).obj
      (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) ⟶ ambientCochainSheafComplex X :=
  (CochainComplex.fromSingle₀Equiv (ambientCochainSheafComplex X)
    (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))).symm
      ⟨ambientConstantsToZeroSheaf X, ambientConstantsToZeroSheaf_coboundary X⟩

#print axioms ambientCupUnitComplexHom
/-- The actual ambient augmentation retains its literal cup-unit component in degree zero.
Source: Hatcher, Algebraic Topology, section 3.2; the degree-zero singular cup unit.
HC no distance; AV milestone no distance.
-/
theorem ambientCupUnitComplexHom_zero (X : TopCat.{0}) :
    (ambientCupUnitComplexHom X).f 0 = ambientConstantsToZeroSheaf X := by
  simp only [ambientCupUnitComplexHom, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]

#print axioms ambientCupUnitComplexHom_zero
/-- Restriction of the actual ambient cup-unit augmentation is the original local singular cochain augmentation as a map of complexes.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.2.
HC no distance; AV milestone no distance.
-/
theorem ambientCupUnitComplexHom_restriction (X : TopCat.{0}) :
    ambientCupUnitComplexHom X ≫ ambientCochainSheafRestriction X =
      constantsToSingularCochainSheafComplex ℚ X := by
  apply HomologicalComplex.Hom.ext
  funext p
  cases p with
  | zero =>
      simp only [HomologicalComplex.comp_f, ambientCupUnitComplexHom_zero,
        constantsToSingularCochainSheafComplex,
        CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      exact ambientConstantsToZeroSheaf_restriction X
  | succ p =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ (p + 1) (by omega)).eq_of_src _ _

#print axioms ambientCupUnitComplexHom_restriction
end HodgeLean.Foundations.RationalHomologyManifold
