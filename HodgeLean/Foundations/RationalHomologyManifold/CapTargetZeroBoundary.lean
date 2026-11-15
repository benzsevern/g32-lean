import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroTerm
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetDifferential
import HodgeLean.Foundations.RationalHomologyManifold.TruncationBoundaryDifferential
import HodgeLean.Foundations.RationalHomologyManifold.RegradedOpcyclesBoundary

/-! The actual first differential in the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The degree-zero cap-target differential is the negative original boundary factored through its actual top-chain quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem capTargetZeroTermIso_boundary (X : TopCat.{0}) (n : ℕ) :
    (capTargetComplex X (n + 1)).d 0 1 ≫
        (capTargetTermIso X (n + 1) 1 n (by omega) (by omega)).hom =
      -((capTargetZeroTermIso X (n + 1)).hom ≫
        (subdivisionLimitSheafComplex X).fromOpcycles (n + 1) n) := by
  let C := subdivisionLimitSheafComplex X
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -((n + 1 : ℕ) : ℤ)
  let e₀ := (K.truncGE b).shiftFunctorObjXIso b 0 b (by omega)
  let e₁ := (K.truncGE b).shiftFunctorObjXIso b 1 (-(n : ℤ)) (by dsimp [b]; omega)
  let a₀ := K.truncGEXIsoOpcycles b
  let a₁ := K.truncGEXIso b (-(n : ℤ)) (by dsimp [b]; omega)
  let c₀ := C.extendOpcyclesIso ComplexShape.embeddingDownNat (j := n + 1) rfl
  let c₁ := C.extendXIso ComplexShape.embeddingDownNat (i := n) rfl
  have hd : (K.truncGE b).d b (-(n : ℤ)) ≫ a₁.hom ≫ c₁.hom =
      a₀.hom ≫ c₀.hom ≫ C.fromOpcycles (n + 1) n := by
    rw [truncGE_d_boundary_of_eq K b (-(n : ℤ)) (by dsimp [b]; omega)]
    change a₀.hom ≫ K.fromOpcycles b (-(n : ℤ)) ≫ a₁.inv ≫ a₁.hom ≫ c₁.hom = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (fun f => a₀.hom ≫ f) (extendDownNat_fromOpcycles C n)
  change (capTargetComplex X (n + 1)).d 0 1 ≫ (e₁ ≪≫ a₁ ≪≫ c₁).hom =
    -((e₀ ≪≫ a₀ ≪≫ c₀).hom ≫ C.fromOpcycles (n + 1) n)
  rw [capTargetComplex_d_signed]
  change ((-1 : ℤ) ^ 1 • (K.truncGE b).d (0 + b) (1 + b)) ≫ (e₁ ≪≫ a₁ ≪≫ c₁).hom =
    -((e₀ ≪≫ a₀ ≪≫ c₀).hom ≫ C.fromOpcycles (n + 1) n)
  simp only [pow_one, neg_one_zsmul, Preadditive.neg_comp]
  apply congrArg (fun f => -f)
  simp only [Iso.trans_hom, Category.assoc]
  change (K.truncGE b).d (0 + b) (1 + b) ≫ e₁.hom ≫ a₁.hom ≫ c₁.hom =
    e₀.hom ≫ a₀.hom ≫ c₀.hom ≫ C.fromOpcycles (n + 1) n
  calc
    _ = (K.truncGE b).d (0 + b) (-(n : ℤ)) ≫ a₁.hom ≫ c₁.hom := by
      simp only [e₁, CochainComplex.shiftFunctorObjXIso, ← Category.assoc,
        HomologicalComplex.d_comp_XIsoOfEq_hom]
    _ = e₀.hom ≫ ((K.truncGE b).d b (-(n : ℤ)) ≫ a₁.hom ≫ c₁.hom) := by
      simp only [e₀, CochainComplex.shiftFunctorObjXIso, ← Category.assoc,
        HomologicalComplex.XIsoOfEq_hom_comp_d]
    _ = _ := by rw [hd]

#print axioms capTargetZeroTermIso_boundary
end HodgeLean.Foundations.RationalHomologyManifold
