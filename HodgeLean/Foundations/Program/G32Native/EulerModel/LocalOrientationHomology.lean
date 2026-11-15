import HodgeLean.Foundations.Program.G32Native.EulerModel.LocalOrientationChains
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass

/-! # The local homology class of the exchanged orientation simplex -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual exchanged-face cycle, expressed using its repeated-vertex boundary and standard cycle. -/
def swappedOrientationCycle (d i : ℕ) (hi : i + 1 < d) :
    ModuleCat.of ℚ ℚ ⟶ (standardLocalRelativeChainComplex ℚ d).cycles d :=
  ((-1 : ℤ) ^ i • foldedOrientationRelativeChain d i hi) ≫
    (standardLocalRelativeChainComplex ℚ d).toCycles (d + 1) d - standardLocalCycle ℚ d

/-- The exchanged-face cycle includes as precisely the actual first distinguished relative face. -/
theorem swappedOrientationCycle_inclusion (d i : ℕ) (hi : i + 1 < d) :
    swappedOrientationCycle d i hi ≫ (standardLocalRelativeChainComplex ℚ d).iCycles d =
      foldedOrientationAmbientFace d i hi ⟨i, by omega⟩ ≫ (standardLocalProjection ℚ d).f d := by
  unfold swappedOrientationCycle
  rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.toCycles_i,
    Preadditive.zsmul_comp, foldedOrientationRelativeChain_boundary_pair,
    smul_smul, ← mul_pow]
  norm_num
  rw [standardLocalCycle_inclusion, foldedOrientationAmbientFace_right]
  exact add_sub_cancel_right _ _

#print axioms swappedOrientationCycle_inclusion

/-- The actual exchanged-face cycle has the negative of the specified standard local homology class. -/
theorem swappedOrientationCycle_homology (d i : ℕ) (hi : i + 1 < d) :
    swappedOrientationCycle d i hi ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d =
      -(standardLocalCycle ℚ d ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d) := by
  unfold swappedOrientationCycle
  rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ,
    comp_zero, zero_sub]

#print axioms swappedOrientationCycle_homology
end HodgeLean.Foundations.Program.G32Native.EulerModel
