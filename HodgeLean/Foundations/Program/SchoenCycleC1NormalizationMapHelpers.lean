import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers

/-! # Generic compatibility of the actual normalization tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatibility on the retained generic source forces the specified
normalization transition to lie over the base transition. -/
theorem s2e_c1_normalization_transition_over
    {T : Scheme} [IsReduced T] (X Y : Over (Spec ↧ℂ)) [IsSeparated Y.hom]
    (b : X ⟶ Y) (ηX : T ⟶ X.left) (ηY : T ⟶ Y.left)
    [QuasiCompact ηX] [QuasiSeparated ηX] [QuasiCompact ηY] [QuasiSeparated ηY]
    (hη : ηX ≫ b.left = ηY)
    (f : s2b_normalizationOver X ηX ⟶ s2b_normalizationOver Y ηY)
    (hf : ηX.toNormalization ≫ f.left = ηY.toNormalization) :
    f ≫ s2b_normalizationMap Y ηY = s2b_normalizationMap X ηX ≫ b := by
  haveI : IsReduced (s2b_normalizationOver X ηX).left :=
    inferInstanceAs (IsReduced ηX.normalization)
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w (f ≫ s2b_normalizationMap Y ηY)).trans
      (Over.w (s2b_normalizationMap X ηX ≫ b)).symm) ηX.toNormalization
  change ηX.toNormalization ≫ (f.left ≫ ηY.fromNormalization) =
    ηX.toNormalization ≫ (ηX.fromNormalization ≫ b.left)
  rw [← Category.assoc, hf, ηY.toNormalization_fromNormalization,
    ← Category.assoc, ηX.toNormalization_fromNormalization]
  exact hη.symm

/-- A transition carrying the retained generic source to the previous
normalization is dominant. -/
theorem s2e_c1_normalization_transition_dominant
    {T : Scheme} (X Y : Over (Spec ↧ℂ))
    (ηX : T ⟶ X.left) (ηY : T ⟶ Y.left)
    [QuasiCompact ηX] [QuasiSeparated ηX] [QuasiCompact ηY] [QuasiSeparated ηY]
    (f : s2b_normalizationOver X ηX ⟶ s2b_normalizationOver Y ηY)
    (hf : ηX.toNormalization ≫ f.left = ηY.toNormalization) : IsDominant f.left := by
  haveI : IsDominant (ηX.toNormalization ≫ f.left) := by
    rw [hf]
    infer_instance
  exact IsDominant.of_comp ηX.toNormalization f.left

end HodgeLean.Foundations.Program
