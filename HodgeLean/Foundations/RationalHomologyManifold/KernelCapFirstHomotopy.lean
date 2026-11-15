import HodgeLean.Foundations.RationalHomologyManifold.KernelCapInteriorHomotopy
import HodgeLean.Foundations.RationalHomologyManifold.KernelCapPrismZeroNormalization

/-! The actual bounded kernel cap homotopy in degree one.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual bounded kernel-prism components satisfy the first positive cap homotopy identity through the top boundary quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_first (X : TopCat.{0}) [RegularSpace X] (q : ℕ)
    (z : (SingularChainComplex ℚ X).X (q + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (q + 1) j z = 0) :
    (ambientLocalZeroSheafInclusion X).f 1 ≫ ambientCapTargetComponent X (q + 1) z 1 =
      (ambientLocalZeroSheafComplex X).d 1 2 ≫ kernelCapTargetPrismComponent X (q + 1) z 1 +
        kernelCapTargetPrismComponent X (q + 1) z 0 ≫ (capTargetComplex X (q + 1)).d 0 1 := by
  let B := ambientLocalZeroSheafComplex X
  let C := subdivisionLimitSheafComplex X
  let e := capTargetTermIso X (q + 1) 1 q (by omega) (by omega)
  let u : B.X 2 ⟶ C.X q := kernelPrismCapSheafMap X (q + 1) 2 q z
  let v : B.X 1 ⟶ C.X (q + 1) := kernelPrismCapSheafMap X (q + 1) 1 (q + 1) z
  have hnext : kernelCapTargetPrismComponent X (q + 1) z 1 ≫ e.hom = -u :=
    kernelCapTargetPrismComponent_positive X (q + 1) 1 q z (by omega) (by omega)
  have hprev := kernelCapTargetPrismComponent_zero X (q + 1) z
  have hbd : (kernelCapTargetPrismComponent X (q + 1) z 0 ≫
      (capTargetComplex X (q + 1)).d 0 1) ≫ e.hom = v ≫ C.d (q + 1) q := by
    rw [Category.assoc, capTargetZeroTermIso_boundary, Preadditive.comp_neg,
      ← Category.assoc, hprev, Preadditive.neg_comp, neg_neg, Category.assoc,
      HomologicalComplex.p_fromOpcycles]
  apply (cancel_mono e.hom).mp
  calc
    _ = (ambientLocalZeroSheafInclusion X).f 1 ≫ ambientFixedCapSheafMap X 1 q
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : q + 1 = 1 + q)).hom z) := by
      rw [Category.assoc, ambientCapTargetComponent_positive X (q + 1) 1 q z (by omega) (by omega)]
    _ = -(B.d 1 2 ≫ u) + v ≫ C.d (q + 1) q := by
      simpa only [pow_one, neg_one_zsmul, sub_neg_eq_add] using
        kernelPrismCapSheaf_identity_cast X (q + 1) 1 q z hz (by omega)
    _ = _ := by
      rw [Preadditive.add_comp, Category.assoc, hnext, hbd, Preadditive.comp_neg]

#print axioms kernelCapTargetPrismComponent_first
end HodgeLean.Foundations.RationalHomologyManifold
