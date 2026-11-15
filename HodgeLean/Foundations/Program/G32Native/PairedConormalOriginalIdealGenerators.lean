import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalChartEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneChartOpens

/-! # Exact normalized original Cartier generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restrict the actual original normalized hyperplane equation to its Cartier chart image. -/
def conormalOriginalHyperplaneGenerator (k : ℕ) (i : Fin (k + 1)) :
    Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), (paired_hyperplaneChartOpen k i).1) :=
  (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map
    (homOfLE (conormal_hyperplane_chartOpen_eq_coordinate k i).le).op
      (conormalOriginalCoordinateRatio k i 0)

/-- The exact original ratio is the normalized polynomial equation in the actual Cartier chart ring. -/
theorem conormal_original_hyperplane_generator_coordinate (k : ℕ) (i : Fin (k + 1)) :
    paired_hyperplaneChartSectionEquiv k i (conormalOriginalHyperplaneGenerator k i) =
      paired_hyperplaneChartEquation k i := by
  have ht : (⊤ : (Spec (CommRingCat.of
      (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).Opens) ≤
      s2e_s2b_chart i ⁻¹ᵁ projectiveSpaceBasicOpen k (X i) := by
    rw [← conormal_hyperplane_chartOpen_eq_coordinate k i]
    change ⊤ ≤ s2e_s2b_chart i ⁻¹ᵁ (s2e_s2b_chart i ''ᵁ ⊤)
    rw [Scheme.Hom.preimage_image_eq]
  have hc : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map
      (homOfLE (conormal_hyperplane_chartOpen_eq_coordinate k i).le).op ≫
        ((s2e_s2b_chart i).appIso ⊤).hom =
      (s2e_s2b_chart i).appLE (projectiveSpaceBasicOpen k (X i)) ⊤ ht := by
    rw [← Scheme.Hom.appLE_appIso_inv (s2e_s2b_chart i) ht,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := ConcreteCategory.congr_hom hc (conormalOriginalCoordinateRatio k i 0)
  change (Scheme.ΓSpecIso (CommRingCat.of
      (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).hom
      (((s2e_s2b_chart i).appIso ⊤).hom (conormalOriginalHyperplaneGenerator k i)) = _
  rw [show ((s2e_s2b_chart i).appIso ⊤).hom (conormalOriginalHyperplaneGenerator k i) =
    (s2e_s2b_chart i).appLE (projectiveSpaceBasicOpen k (X i)) ⊤ ht
      (conormalOriginalCoordinateRatio k i 0) from hv]
  exact conormal_original_ratio_chart_evaluation k i 0 ht

/-- The actual normalized ratio generates the original hyperplane ideal on its Cartier chart. -/
theorem conormal_original_hyperplane_ideal_principal (k : ℕ) (i : Fin (k + 1)) :
    (s2e_hyperplaneIdeal k).ideal (paired_hyperplaneChartOpen k i) =
      Ideal.span {conormalOriginalHyperplaneGenerator k i} := by
  have he : conormalOriginalHyperplaneGenerator k i =
      (paired_hyperplaneChartSectionEquiv k i).symm (paired_hyperplaneChartEquation k i) :=
    (paired_hyperplaneChartSectionEquiv k i).eq_symm_apply.mpr
      (conormal_original_hyperplane_generator_coordinate k i)
  rw [he]
  exact paired_hyperplaneChartIdeal_principal k i

/-- Any affine presentation of the same original coordinate open has the same literal ratio generator. -/
theorem conormal_original_hyperplane_ideal_principal_on_coordinate
    (k : ℕ) (i : Fin (k + 1))
    (U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens)
    (hU : U.1 = projectiveSpaceBasicOpen k (X i)) :
    (s2e_hyperplaneIdeal k).ideal U = Ideal.span
      {(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map
        (homOfLE hU.le).op (conormalOriginalCoordinateRatio k i 0)} := by
  have hUc : U = paired_hyperplaneChartOpen k i :=
    Subtype.ext (hU.trans (conormal_hyperplane_chartOpen_eq_coordinate k i).symm)
  subst U
  exact conormal_original_hyperplane_ideal_principal k i

end HodgeLean.Foundations.Program.G32Native
