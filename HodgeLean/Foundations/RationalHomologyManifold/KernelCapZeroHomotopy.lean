import HodgeLean.Foundations.RationalHomologyManifold.KernelCapFirstHomotopy

/-! The actual bounded kernel cap homotopy in degree zero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In degree zero the incoming prism boundary vanishes in the actual top-chain quotient, leaving the first kernel homotopy term.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_initial (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    (ambientLocalZeroSheafInclusion X).f 0 ≫ ambientCapTargetComponent X N z 0 =
      (ambientLocalZeroSheafComplex X).d 0 1 ≫ kernelCapTargetPrismComponent X N z 0 := by
  let C := subdivisionLimitSheafComplex X
  apply (cancel_mono (capTargetZeroTermIso X N).hom).mp
  rw [Category.assoc, ambientCapTargetComponent_zero, ← Category.assoc]
  rw [kernelPrismCapSheaf_identity_cast X N 0 N z hz (by omega)]
  rw [Preadditive.sub_comp, Preadditive.neg_comp, Preadditive.zsmul_comp,
    Category.assoc]
  simp only [Category.assoc, HomologicalComplex.d_pOpcycles, comp_zero, smul_zero, sub_zero]
  rw [kernelCapTargetPrismComponent_zero, Preadditive.comp_neg]

#print axioms kernelCapTargetPrismComponent_initial
end HodgeLean.Foundations.RationalHomologyManifold
