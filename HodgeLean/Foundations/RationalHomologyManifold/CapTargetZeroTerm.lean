import HodgeLean.Foundations.RationalHomologyManifold.CapTargetTerms

/-! The actual boundary quotient in degree zero of the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The degree-zero cap target is the actual top-chain quotient by the incoming boundary.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; good truncation at the orientation degree.
HC no distance; AV milestone no distance.
-/
def capTargetZeroTermIso (X : TopCat.{0}) (N : ℕ) :
    (capTargetComplex X N).X 0 ≅ (subdivisionLimitSheafComplex X).opcycles N := by
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -(N : ℤ)
  change ((K.truncGE b)⟦b⟧).X (0 : ℤ) ≅ _
  exact (K.truncGE b).shiftFunctorObjXIso b 0 b (by omega) ≪≫
    K.truncGEXIsoOpcycles b ≪≫
      (subdivisionLimitSheafComplex X).extendOpcyclesIso ComplexShape.embeddingDownNat rfl

#print axioms capTargetZeroTermIso
end HodgeLean.Foundations.RationalHomologyManifold
