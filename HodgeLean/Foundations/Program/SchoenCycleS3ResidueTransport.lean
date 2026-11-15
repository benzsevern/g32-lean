import HodgeLean.Foundations.Program.SchoenCycleS3HyperplaneDensity
import HodgeLean.Foundations.Program.SchoenCycleS3StrictRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2e_residue_strict_restriction {X Y : Scheme} (k : ℕ)
    (j t : Fin (k + 1)) (htj : t ≠ j) (f : X ⟶ Y)
    (ℓ : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ⟶ X)
    (D K : Y.IdealSheafData)
    (hD : (D.comap f).comap ℓ = s2e_s2b_residueIdeal k j)
    (hK : (K.comap f).comap ℓ = s2e_s2b_residueIdeal k t) :
    (s2c_strictTransform f D K).comap ℓ = s2e_s2b_residueIdeal k j := by
  rw [← hD]
  apply s2e_strictTransform_restriction_of_density
  · rw [hD]
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.IdealSheafData.radical_ideal, s2e_s2b_residueIdeal,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact (PrimeSpectrum.isRadical_vanishingIdeal
      (R := Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)) _).radical
  · have hsD : (ℓ ≫ f) ⁻¹' ((D.support : Set Y)) =
        ((s2e_s2b_residueIdeal k j).support : Set _) := by
      have hh := congrArg (fun I : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData =>
        (I.support : Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))) hD
      simpa only [Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, Set.preimage_preimage,
        Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_def] using hh
    have hsK : (ℓ ≫ f) ⁻¹' ((K.support : Set Y)) =
        ((s2e_s2b_residueIdeal k t).support : Set _) := by
      have hh := congrArg (fun I : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData =>
        (I.support : Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))) hK
      simpa only [Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, Set.preimage_preimage,
        Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_def] using hh
    rw [hD, Set.preimage_diff, hsD, hsK]
    exact s2e_distinct_residue_dense k j t htj

end HodgeLean.Foundations.Program
