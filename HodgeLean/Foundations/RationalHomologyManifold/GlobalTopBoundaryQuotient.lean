import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionGlobalSections

/-! Actual global epimorphy of the top supported-chain boundary quotient.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Global sections retain the actual top supported-chain boundary quotient as an epimorphism.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; soft boundary-image lifting at the orientation degree.
HC no distance; AV milestone no distance.
-/
theorem subdivisionGlobal_top_pOpcycles_epi (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1)) :
    Epi ((subdivisionGlobalSectionsFunctor X).map
      ((subdivisionLimitSheafComplex X).pOpcycles (n + 1))) := by
  let C := subdivisionLimitSheafComplex X
  let E := subdivisionGlobalSectionsFunctor X
  letI : PreservesColimit (parallelPair (C.sc (n + 1)).f 0) E := by
    change PreservesColimit (parallelPair (C.d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)) 0) E
    rw [ChainComplex.prev]
    exact subdivision_boundary_global_preservesCokernel X t (n + 1) n o le_rfl
  letI : E.PreservesRightHomologyOf (C.sc (n + 1)) :=
    ⟨fun h => { f := inferInstance, g' := inferInstance }⟩
  change Epi (((C.sc (n + 1)).rightHomologyData.map E).p)
  infer_instance

#print axioms subdivisionGlobal_top_pOpcycles_epi
end HodgeLean.Foundations.RationalHomologyManifold
