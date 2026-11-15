import HodgeLean.Foundations.RationalHomologyManifold.CapTargetComplex

/-! Actual term identifications of the bounded fixed-cycle cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In a positive complementary degree, the cap target is the original supported subdivision chain sheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual term identifications under good truncation and regrading.
HC no distance; AV milestone no distance.
-/
def capTargetTermIso (X : TopCat.{0}) (N p q : ℕ) (hp : 0 < p) (hN : p + q = N) :
    (capTargetComplex X N).X p ≅ (subdivisionLimitSheafComplex X).X q := by
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -(N : ℤ)
  change ((K.truncGE b)⟦b⟧).X (p : ℤ) ≅ _
  exact (K.truncGE b).shiftFunctorObjXIso b (p : ℤ) (-(q : ℤ)) (by dsimp [b]; omega) ≪≫
    K.truncGEXIso b (-(q : ℤ)) (by dsimp [b]; omega) ≪≫
      (subdivisionLimitSheafComplex X).extendXIso ComplexShape.embeddingDownNat rfl

#print axioms capTargetTermIso
end HodgeLean.Foundations.RationalHomologyManifold
