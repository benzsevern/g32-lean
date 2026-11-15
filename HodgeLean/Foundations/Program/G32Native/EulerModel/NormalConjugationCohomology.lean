import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPairedPermutation
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass

/-! # Supported cohomology of the specified normal conjugation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual real pair-exchange composition transported through the specified complex-real pair isomorphism. -/
def rotatedNormalConjugationPair (k : ℕ) : puncturedPair ℂ k ⟶ puncturedPair ℂ k :=
  (standardComplexRealPairIso k).hom ≫
    orientationSwapListMap (k * 2) (orientationPairedSwapList k) ≫
      (standardComplexRealPairIso k).inv

/-- The transported pair map is exactly multiplication of the specified normal conjugation by `I`. -/
theorem rotatedNormalConjugationPair_apply (k : ℕ) (z : Fin k → ℂ) :
    (TopPair.Hom.fst (rotatedNormalConjugationPair k)) z =
      fun j => Complex.I * normalConjugation k z j := by
  change (complexRealHomeomorph k).symm
      ((TopPair.Hom.fst (orientationSwapListMap (k * 2) (orientationPairedSwapList k)))
        (complexRealHomeomorph k z)) = _
  apply (complexRealHomeomorph k).injective
  rw [Homeomorph.apply_symm_apply]
  exact orientationPairedSwaps_realCoordinates k z

#print axioms rotatedNormalConjugationPair_apply

/-- The actual rotated normal conjugation has the exact parity action on supported cohomology. -/
theorem rotatedNormalConjugationPair_cohomology (k : ℕ)
    (α : RelativeCohomology ℚ (puncturedPair ℂ k) (k * 2)) :
    relativeCohomologyMap ℚ (k * 2) (rotatedNormalConjugationPair k) α = (-1 : ℚ) ^ k • α := by
  unfold rotatedNormalConjugationPair
  rw [relativeCohomologyMap_comp, LinearMap.comp_apply,
    relativeCohomologyMap_comp, LinearMap.comp_apply,
    orientationPairedSwaps_relativeCohomology, map_smul,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.hom_inv_id, relativeCohomologyMap_id, LinearMap.id_apply]

#print axioms rotatedNormalConjugationPair_cohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
