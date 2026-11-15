import HodgeLean.Foundations.RationalHomologyManifold.CapTargetComplex

/-! The actual bounded range of the regraded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Above the fixed total dimension, the actual cap target has zero terms.
Source: Bredon, Sheaf Theory, second edition, VI.12; nonnegative supported chains and their cap regrading.
HC no distance; AV milestone no distance.
-/
theorem capTargetComplex_isZero_above (X : TopCat.{0}) (N p : ℕ) (hp : N < p) :
    IsZero ((capTargetComplex X N).X p) := by
  let C := subdivisionLimitSheafComplex X
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -(N : ℤ)
  let i : ℤ := (p : ℤ) + b
  have hz : IsZero (K.X i) := by
    change IsZero ((C.extend ComplexShape.embeddingDownNat).X i)
    apply C.isZero_extend_X ComplexShape.embeddingDownNat i
    intro j hj
    change -(j : ℤ) = i at hj
    dsimp [i, b] at hj
    omega
  change IsZero ((K.truncGE b).X i)
  exact IsZero.of_iso hz (K.truncGEXIso b i (by dsimp [i]; omega))

#print axioms capTargetComplex_isZero_above
end HodgeLean.Foundations.RationalHomologyManifold
