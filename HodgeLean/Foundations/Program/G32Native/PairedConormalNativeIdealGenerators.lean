import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalIdealGenerators
import HodgeLean.Foundations.Program.G32Native.PairedConormalPrincipalPullback

/-! # Literal principal generators of the actual native hyperplane ideal -/
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

/-- The actual native reduced hyperplane ideal is generated on each standard
chart by the literal normalized ratio used in the original relation-row calculation. -/
theorem conormal_native_hyperplane_ideal_principal (k : ℕ) (i : Fin (k + 1)) :
    (conormalNativeHyperplaneIdeal ℂ k).ideal (conormalNativeCoordinateOpen ℂ k i) =
      Ideal.span {ProjSpace.coordinateRatioSection ℂ k i 0} := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  let U := conormalNativeCoordinateOpen ℂ k i
  have hV : f ''ᵁ U.1 = projectiveSpaceBasicOpen k (X i) := by
    change f ''ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) = _
    rw [← conormal_polynomialProjectiveSpaceIso_preimage_coordinate k i]
    change f ''ᵁ (f ⁻¹ᵁ projectiveSpaceBasicOpen k (X i)) = _
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  let V : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens :=
    ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  let a := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map
    (homOfLE hV.le).op (conormalOriginalCoordinateRatio k i 0)
  have ha := conormal_original_hyperplane_ideal_principal_on_coordinate k i V hV
  have hp : (conormalNativeHyperplaneIdeal ℂ k).ideal U =
      Ideal.span {((f.appIso U.1).hom).hom a} := by
    rw [← conormal_polynomial_hyperplane_comap]
    exact conormal_principal_ideal_open_pullback f (s2e_hyperplaneIdeal k) U a ha
  have hb : U.1 ≤ f ⁻¹ᵁ projectiveSpaceBasicOpen k (X i) := by
    rw [conormal_polynomialProjectiveSpaceIso_preimage_coordinate]
    rfl
  have hc : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map (homOfLE hV.le).op ≫
      (f.appIso U.1).hom = f.appLE (projectiveSpaceBasicOpen k (X i)) U.1 hb := by
    rw [← Scheme.Hom.appLE_appIso_inv f hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := ConcreteCategory.congr_hom hc (conormalOriginalCoordinateRatio k i 0)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hv
  have hr : ((f.appIso U.1).hom).hom a = ProjSpace.coordinateRatioSection ℂ k i 0 := by
    convert! hv.trans (conormal_original_coordinate_ratio_pullback k i 0) using 1
  rw [hp, hr]
  rfl

end HodgeLean.Foundations.Program.G32Native
