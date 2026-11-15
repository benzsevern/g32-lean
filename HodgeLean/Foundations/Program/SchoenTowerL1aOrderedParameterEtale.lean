import HodgeLean.Foundations.Program.SchoenTowerL1aAffinePowerCoordinates

/-! # Polynomial etaleness on actual ordered curve powers

Implication from an actual etale curve parameter to the polynomial evaluation
map on its retained ordered power. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Ordered powers of an actual affine scheme over the complex base are affine.
Source: Hartshorne, Algebraic Geometry, II.3, affine fibre products. -/
theorem s2v_l1a_ordered_power_affine (U : Over (Spec ↧ℂ)) [IsAffine U.left] (n : ℕ) :
    IsAffine (g3_power U n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsAffine (Spec ↧ℂ))
  | succ n ih =>
      letI := ih
      change IsAffine (CategoryTheory.Limits.pullback U.hom (g3_power U n).hom)
      infer_instance

/-- The actual polynomial map in the coordinatewise pullbacks of an etale
curve parameter is etale on every retained ordered power.
Source: Hartshorne, Algebraic Geometry, III.10, products of etale morphisms. -/
theorem s2v_l1a_ordered_parameter_etale
    (U : Over (Spec ↧ℂ)) [IsAffine U.left] (z : Γ(U.left, ⊤))
    (hEt : (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)).Etale)
    (n : ℕ) :
    (MvPolynomial.eval₂Hom (g3_power U n).hom.appTop.hom
      (fun j => (g3_proj U n j).left.appTop.hom z)).Etale := by
  let L := Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
  obtain ⟨f, hf, hz⟩ := s2v_l1a_parameter_morphism U (Fin 1) (fun _ => z) hEt
  letI : Etale f.left := hf
  obtain ⟨e, he⟩ := s2v_l1a_affine_line_power_coordinates n
  let F := s2_powerMap f n ≫ e.hom
  letI : IsAffine (g3_power U n).left := s2v_l1a_ordered_power_affine U n
  letI : Etale (s2_powerMap f n).left := s2v_l1a_ordered_power_etale f n
  letI : Etale F.left := by
    change Etale ((s2_powerMap f n).left ≫ e.hom.left)
    infer_instance
  have hproj (j : Fin n) : s2_powerMap f n ≫ g3_proj L n j =
      g3_proj U n j ≫ f := s2_check_lift_proj n _ j
  have hcoords (j : Fin n) : F.left.appTop (AffineSpace.coord (Spec ↧ℂ) j) =
      (g3_proj U n j).left.appTop.hom z := by
    change (s2_powerMap f n ≫ e.hom).left.appTop _ = _
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, he]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    change (s2_powerMap f n ≫ g3_proj L n j).left.appTop _ = _
    rw [hproj, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hz]
  have H := s2v_l1a_affineSpace_section_polynomial_etale (g3_power U n) (Fin n) F
  have hc : (fun j => F.left.appTop
      ((s2t_affineSpacePolynomialEquiv (Fin n)) (MvPolynomial.X j))) =
      (fun j => (g3_proj U n j).left.appTop.hom z) := by
    funext j
    have hj : (s2t_affineSpacePolynomialEquiv (Fin n)) (MvPolynomial.X j) =
        AffineSpace.coord (Spec ↧ℂ) j := SpecIso_hom_appTop_X j
    rw [hj, hcoords]
  rw [hc] at H
  rw [s2v_l1a_structure_section_coefficients]
  exact s2v_l1a_etale_eval_change_coefficients _ _ _ H

end HodgeLean.Foundations.Program
