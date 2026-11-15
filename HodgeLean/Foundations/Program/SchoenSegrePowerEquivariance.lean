import HodgeLean.Foundations.Program.SchoenSegrePermutationSections
import HodgeLean.Foundations.Program.SchoenProjUnitEvaluationNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual finite-factor Segre chart morphisms intertwine chart reindexing with the graded tuple-coordinate scheme map. -/
theorem s2_segrePowerChartMap_permute (d n : ℕ) (a : Fin n → Fin (d + 1))
    (σ : Equiv.Perm (Fin n)) :
    s2_segrePowerChartPerm d n a σ ≫
        s2_segrePowerChartMap d n (fun i => a (σ.symm i)) =
      s2_segrePowerChartMap d n a ≫ s2_segreCoordinateMap (ULift.{0} ℤ) d n σ := by
  let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)
  let f := s2_segreCoordinateRename (ULift.{0} ℤ) d n σ
  let hf := b54_irrelevant_le_map_of_surjective f
    (s2_segreCoordinateRename_surjective (ULift.{0} ℤ) d n σ)
  have hPull : (HomogeneousIdeal.irrelevant 𝒢).toIdeal.map
      ((s2_segrePowerChartPerm d n a σ).appTop.hom.comp
        (s2_segrePowerSections d n (fun i => a (σ.symm i)))) = ⊤ := by
    rw [← Ideal.map_map, s2_segrePowerSections_irrelevant, Ideal.map_top]
  have hComp : (HomogeneousIdeal.irrelevant 𝒢).toIdeal.map
      ((s2_segrePowerSections d n a).comp f.toRingHom) = ⊤ := by
    rw [← s2_segrePowerChartPerm_sections]
    exact hPull
  have hφ : s2_segrePowerSections d n a (f (X (fun i => a (σ.symm i)))) = 1 := by
    simpa only [f, s2_segreCoordinateRename_X, Equiv.symm_apply_apply] using
      s2_segrePowerSections_X_self d n a
  change s2_segrePowerChartPerm d n a σ ≫ Proj.fromOfGlobalSections 𝒢
      (s2_segrePowerSections d n (fun i => a (σ.symm i))) _ =
    Proj.fromOfGlobalSections 𝒢 (s2_segrePowerSections d n a) _ ≫ Proj.map f hf
  rw [spec_g3c_comp_fromOfGlobalSections_aux 𝒢 (s2_segrePowerChartPerm d n a σ) _ _ hPull,
    s2_fromGlobalSections_comp_map_of_unit 𝒢 𝒢 f hf (s2_segrePowerChart d n a)
      (s2_segrePowerSections d n a) (s2_segrePowerSections_irrelevant d n a) hComp
      (isHomogeneous_X _ (fun i => a (σ.symm i))) zero_lt_one hφ]
  congr 1
  exact s2_segrePowerChartPerm_sections d n a σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-factor integral Segre morphism intertwines every factor permutation with its graded coordinate scheme map. -/
theorem s2_segrePowerMap_permute (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_segrePowerPerm d n σ ≫ s2_segrePowerMap d n =
      s2_segrePowerMap d n ≫ s2_segreCoordinateMap (ULift.{0} ℤ) d n σ := by
  apply (s2_segrePowerCover d n).hom_ext
  intro a
  change s2_segrePowerChartι d n a ≫ (s2_segrePowerPerm d n σ ≫ s2_segrePowerMap d n) =
    s2_segrePowerChartι d n a ≫ (s2_segrePowerMap d n ≫ s2_segreCoordinateMap (ULift.{0} ℤ) d n σ)
  rw [← Category.assoc, s2_segrePowerChartPerm_ι, Category.assoc, s2_segrePowerChartι_map,
    ← Category.assoc, s2_segrePowerChartι_map]
  exact s2_segrePowerChartMap_permute d n a σ

end HodgeLean.Foundations.Program
