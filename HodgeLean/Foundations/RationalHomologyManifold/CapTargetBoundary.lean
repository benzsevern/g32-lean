import HodgeLean.Foundations.RationalHomologyManifold.CapTargetTerms
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetDifferential
import HodgeLean.Foundations.RationalHomologyManifold.TruncationDifferential

/-! Actual boundary compatibility of the bounded cap-target term identifications.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In positive complementary degrees, the actual cap-target differential is the original supported-chain boundary with the fixed-cycle sign.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem capTargetTermIso_boundary (X : TopCat.{0}) (N p q : ℕ) (hp : 0 < p)
    (hN : p + (q + 1) = N) :
    (capTargetComplex X N).d p (p + 1) ≫
        (capTargetTermIso X N (p + 1) q (by omega) (by omega)).hom =
      (-1 : ℤ) ^ (p + 1) • ((capTargetTermIso X N p (q + 1) hp hN).hom ≫
        (subdivisionLimitSheafComplex X).d (q + 1) q) := by
  let C := subdivisionLimitSheafComplex X
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -(N : ℤ)
  let e₁ := (K.truncGE b).shiftFunctorObjXIso b (p : ℤ) (-((q + 1 : ℕ) : ℤ)) (by dsimp [b]; omega)
  let e₂ := (K.truncGE b).shiftFunctorObjXIso b ((p + 1 : ℕ) : ℤ) (-(q : ℤ)) (by dsimp [b]; omega)
  let a₁ := K.truncGEXIso b (-((q + 1 : ℕ) : ℤ)) (by dsimp [b]; omega)
  let a₂ := K.truncGEXIso b (-(q : ℤ)) (by dsimp [b]; omega)
  let c₁ := C.extendXIso ComplexShape.embeddingDownNat (i := q + 1) rfl
  let c₂ := C.extendXIso ComplexShape.embeddingDownNat (i := q) rfl
  have hd : (K.truncGE b).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ a₂.hom ≫ c₂.hom =
      a₁.hom ≫ c₁.hom ≫ C.d (q + 1) q := by
    rw [truncGE_d_via_termIso K b _ _ (by dsimp [b]; omega) (by dsimp [b]; omega) (by omega)]
    change a₁.hom ≫ K.d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ a₂.inv ≫ a₂.hom ≫ c₂.hom = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change a₁.hom ≫ (C.extend ComplexShape.embeddingDownNat).d _ _ ≫ c₂.hom = _
    have he := C.extend_d_eq ComplexShape.embeddingDownNat
      (i' := -((q + 1 : ℕ) : ℤ)) (j' := ComplexShape.embeddingDownNat.f q)
      (i := q + 1) (j := q) rfl rfl
    have ht := congrArg (fun f => a₁.hom ≫ f ≫ c₂.hom) he
    exact ht.trans (by
      change a₁.hom ≫ (c₁.hom ≫ C.d (q + 1) q ≫ c₂.inv) ≫ c₂.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  change (capTargetComplex X N).d p (p + 1) ≫ (e₂ ≪≫ a₂ ≪≫ c₂).hom =
    (-1 : ℤ) ^ (p + 1) • ((e₁ ≪≫ a₁ ≪≫ c₁).hom ≫ C.d (q + 1) q)
  rw [capTargetComplex_d_signed, Preadditive.zsmul_comp]
  apply congrArg (fun f => (-1 : ℤ) ^ (p + 1) • f)
  simp only [Iso.trans_hom, Category.assoc]
  change (K.truncGE b).d ((p : ℤ) + b) (((p + 1 : ℕ) : ℤ) + b) ≫ e₂.hom ≫ a₂.hom ≫ c₂.hom =
    e₁.hom ≫ a₁.hom ≫ c₁.hom ≫ C.d (q + 1) q
  calc
    _ = (K.truncGE b).d ((p : ℤ) + b) (-(q : ℤ)) ≫ a₂.hom ≫ c₂.hom := by
      simp only [e₂, CochainComplex.shiftFunctorObjXIso, ← Category.assoc,
        HomologicalComplex.d_comp_XIsoOfEq_hom]
    _ = e₁.hom ≫ ((K.truncGE b).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ a₂.hom ≫ c₂.hom) := by
      simp only [e₁, CochainComplex.shiftFunctorObjXIso, ← Category.assoc,
        HomologicalComplex.XIsoOfEq_hom_comp_d]
    _ = _ := by rw [hd]

#print axioms capTargetTermIso_boundary
end HodgeLean.Foundations.RationalHomologyManifold
