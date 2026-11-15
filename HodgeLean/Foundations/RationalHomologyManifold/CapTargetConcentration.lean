import HodgeLean.Foundations.RationalHomologyManifold.CapTargetComplex
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-! Positive-degree concentration of the actual bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual bounded cap target has zero homology in every positive cochain degree under local orientation concentration.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; concentration of the local chain model.
HC no distance; AV milestone no distance.
-/
theorem capTargetComplex_homology_positive_isZero (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (o : LocalRationalOrientation X N) (p : ℕ) :
    IsZero ((capTargetComplex X N).homology (p + 1)) := by
  let C := TopCat.Sheaf AddCommGrpCat.{0} X
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -(N : ℤ)
  let T := K.truncGE b
  let R := T⟦b⟧
  letI : QuasiIso (K.πTruncGE b) := subdivisionTruncation_quasiIso X N o
  have hT (i : ℤ) (hi : i ≠ b) : IsZero (T.homology i) := by
    apply (asIso (HomologicalComplex.homologyMap (K.πTruncGE b) i)).isZero_iff.mp
    exact subdivisionLimitSheafCochainHomology_concentrated X N o i hi
  have hR : IsZero (R.homology ((p + 1 : ℕ) : ℤ)) := by
    exact IsZero.of_iso (hT (b + ((p + 1 : ℕ) : ℤ)) (by omega))
      (((HomologicalComplex.homologyFunctor C (.up ℤ) (0 : ℤ)).shiftIso b
        ((p + 1 : ℕ) : ℤ) _ rfl).app T)
  let e := R.restrictionHomologyIso ComplexShape.embeddingUpNat p (p + 1) (p + 2)
    (CochainComplex.prev_nat_succ p) (CochainComplex.next ℕ (p + 1))
    (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) (k' := ((p + 2 : ℕ) : ℤ))
    rfl rfl rfl (by rw [CochainComplex.prev]; omega)
    (by rw [CochainComplex.next]; omega)
  have hu : IsZero ((capUnnormalizedTargetComplex X N).homology (p + 1)) :=
    IsZero.of_iso hR e
  exact IsZero.of_iso hu
    ((HomologicalComplex.homologyFunctor C (.up ℕ) (p + 1)).mapIso
      (capTargetComplexIso X N)).symm

#print axioms capTargetComplex_homology_positive_isZero
end HodgeLean.Foundations.RationalHomologyManifold
