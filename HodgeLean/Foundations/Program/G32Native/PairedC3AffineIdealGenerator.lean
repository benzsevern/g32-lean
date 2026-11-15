import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineComparisonSections

/-! # Original ideal sections in their associated affine module -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The natural affine ideal comparison sends the actual ideal section to
the associated section of its original ring-kernel element. -/
theorem paired_c3_affine_ideal_generator_section
    (R S : CommRingCat.{0}) (p : R ⟶ S)
    (x : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map p))) :
    (Conormal.affineIdealIso R S p).hom.app ⊤ x =
      (tilde.adjunction (R := R)).unit.app (ModuleCat.of R (RingHom.ker p.hom))
        (s2e_affine_ideal_sections_equiv R S p x) := by
  let E := Conormal.affineIdealIso R S p
  let e := s2e_affine_ideal_sections_equiv R S p
  have h := Conormal.affineIdealIso_inv_transpose R S p _ E.hom
  rw [E.inv_hom_id] at h
  change (tilde.adjunction (R := R)).unit.app (ModuleCat.of R (RingHom.ker p.hom)) =
    e.symm.toModuleIso.hom ≫ (moduleSpecΓFunctor (R := R)).map E.hom at h
  have hx := congrArg (fun f => f (e x)) h
  change (tilde.adjunction (R := R)).unit.app (ModuleCat.of R (RingHom.ker p.hom)) (e x) =
    (moduleSpecΓFunctor (R := R)).map E.hom (e.symm (e x)) at hx
  rw [e.symm_apply_apply] at hx
  exact hx.symm

#print axioms paired_c3_affine_ideal_generator_section
end HodgeLean.Foundations.Program.G32Native
