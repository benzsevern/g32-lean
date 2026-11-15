import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoefficientHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1aSectionParameterRestriction

/-! # Principal restrictions of polynomial coordinate sections

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
attribute [local instance] overSpecAlgebra

/-- A principal etale coefficient presentation gives an actual chart with its original section values.
Source: Hartshorne, Algebraic Geometry, II.2 and III.10.
HC no distance; AV milestone no distance.
-/
theorem principal_section_coordinates (Y : Over (Spec ↧ℂ)) [IsAffine Y.left]
    (n : ℕ) (c : Fin n → Γ(Y.left, ⊤)) (d : Γ(Y.left, ⊤))
    (hEt : ((algebraMap Γ(Y.left, ⊤) (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) c).toRingHom).Etale) :
    ∃ f : ComplexPoint.openScheme Y (Y.left.basicOpen d) ⟶ affine n,
      Etale f.left ∧ ∀ (p : ComplexPoint (ComplexPoint.openScheme Y (Y.left.basicOpen d))) j,
        coordinateValue n (Point.map f p) j = Point.evaluate ⊤ (c j)
          (Point.map (ComplexPoint.openInclusion Y (Y.left.basicOpen d)) p) := by
  let W := Y.left.basicOpen d
  let X := ComplexPoint.openScheme Y W
  let r : X ⟶ Y := ComplexPoint.openInclusion Y W
  letI : IsAffine X.left := (isAffineOpen_top Y.left).basicOpen d
  letI := overSpecAlgebra X ⊤
  let c' := fun i => r.left.appTop.hom (c i)
  have hE := s2v_l1a_etale_principal_section_parameters r c d
    (s2v_l1a_openScheme_sections_localization Y.left d) hEt
  have hEC : (MvPolynomial.aeval (R := ℂ) c').toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hE
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hE
  let G := MvPolynomial.aeval (R := ℂ) c'
  let f : X ⟶ affine n := s2e_section_defined_affine_map X _ G
  haveI : Etale f.left := by
    haveI : Etale (Spec.map (CommRingCat.ofHom G.toRingHom)) :=
      HasRingHomProperty.Spec_iff.mpr hEC
    change Etale (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom))
    infer_instance
  refine ⟨f, inferInstance, ?_⟩
  intro p j
  rw [section_map_coordinate_value]
  change Point.evaluate ⊤ ((MvPolynomial.aeval (R := ℂ) c') (MvPolynomial.X j)) p = _
  rw [MvPolynomial.aeval_X]
  have H := Point.evaluate_map r ⊤ (c j) p
  simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop] using H.symm

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
