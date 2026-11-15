import HodgeLean.Foundations.Program.G32Native.AffineBlowupGeneratorCover
import HodgeLean.Foundations.Program.G32Native.BlowupChartProjectiveMap
import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousGluing

/-! The opens detected by the global projective coordinates on an affine base chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coordinate open pulls back to the blow-up chart of its generator. -/
theorem g32l4_blowUp_coordinateMap_preimage {R : Type} [CommRing R]
    (I : Ideal R) (m : ℕ) (g : Fin (m + 1) → I)
    (hg : Ideal.span (Set.range (fun k => (g k : R))) = I)
    {Y : Scheme.{0}} (ι : affineBlowUp I ⟶ Y)
    (f : Y ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)))
    (hf : ∀ p, affineBlowUp.chart I (g p) ≫ ι ≫ f =
      g32l4_blowUp_chart_projectiveMap I m g p) (k : Fin (m + 1)) :
    (ι ≫ f) ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)) (X k) =
      (affineBlowUp.chart I (g k)).opensRange := by
  apply n2b_opens_eq_of_cover_preimage (g32l4_affine_blowUp_generatorCover I g hg).openCover
  intro p
  change affineBlowUp.chart I (g p) ⁻¹ᵁ ((ι ≫ f) ⁻¹ᵁ _) =
    affineBlowUp.chart I (g p) ⁻¹ᵁ (affineBlowUp.chart I (g k)).opensRange
  rw [← Scheme.Hom.comp_preimage, hf p]
  unfold g32l4_blowUp_chart_projectiveMap
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one (isHomogeneous_X _ k),
    eval₂Hom_X', affineBlowUp.chart_preimage_chart]
  exact basicOpen_eq_of_affine _

end HodgeLean.Foundations.Program
