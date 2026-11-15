import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroBoundary

/-! Actual initial homology of the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original top-chain homology includes as the actual kernel of the first bounded cap differential through the specified boundary-quotient identification.
Source: Bredon, Sheaf Theory, second edition, VI.12; good truncation at the orientation degree.
HC no distance; AV milestone no distance.
-/
def capTargetInitialKernel (X : TopCat.{0}) (n : ℕ) :
    IsLimit (KernelFork.ofι (f := (capTargetComplex X (n + 1)).d 0 1)
      ((subdivisionLimitSheafComplex X).homologyι (n + 1) ≫ (capTargetZeroTermIso X (n + 1)).inv)
      (by
        apply (cancel_mono (capTargetTermIso X (n + 1) 1 n (by omega) (by omega)).hom).mp
        simp only [Category.assoc, capTargetZeroTermIso_boundary, Preadditive.comp_neg,
          Iso.inv_hom_id_assoc, HomologicalComplex.homologyι_comp_fromOpcycles, neg_zero, zero_comp])) := by
  let C := subdivisionLimitSheafComplex X
  let A := capTargetComplex X (n + 1)
  let e := capTargetZeroTermIso X (n + 1)
  let e' := capTargetTermIso X (n + 1) 1 n (by omega) (by omega)
  apply KernelFork.isLimitOfIsLimitOfIff
    (C.homologyIsKernel (n + 1) n (ChainComplex.next_nat_succ n)) (A.d 0 1) e.symm
  intro W φ
  have he : (φ ≫ e.inv ≫ A.d 0 1) ≫ e'.hom = -(φ ≫ C.fromOpcycles (n + 1) n) := by
    dsimp only [e, e', A, C]
    simp only [Category.assoc, capTargetZeroTermIso_boundary, Preadditive.comp_neg,
      Iso.inv_hom_id_assoc]
  rw [← cancel_mono e'.hom, zero_comp]
  change φ ≫ C.fromOpcycles (n + 1) n = 0 ↔ (φ ≫ e.inv ≫ A.d 0 1) ≫ e'.hom = 0
  rw [he, neg_eq_zero]

#print axioms capTargetInitialKernel
/-- Initial homology of the actual bounded cap complex is the original supported-chain homology in the total degree.
Source: Bredon, Sheaf Theory, second edition, VI.12; the initial kernel of good truncation.
HC no distance; AV milestone no distance.
-/
def capTargetInitialHomologyIso (X : TopCat.{0}) (n : ℕ) :
    (capTargetComplex X (n + 1)).homology 0 ≅
      (subdivisionLimitSheafComplex X).homology (n + 1) :=
  (CochainComplex.isoHomologyπ₀ (capTargetComplex X (n + 1))).symm ≪≫
    ((capTargetInitialKernel X n).conePointUniqueUpToIso
      ((capTargetComplex X (n + 1)).cyclesIsKernel 0 1 (CochainComplex.next ℕ 0))).symm

#print axioms capTargetInitialHomologyIso
end HodgeLean.Foundations.RationalHomologyManifold
