import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveIntegral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Algebra.MvPolynomial.Equiv

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every stalk of the complex projective line is a Dedekind domain.
Source: the standard affine charts are polynomial lines and their stalks are localizations. -/
theorem s0_projective_line_stalk_dedekind
    (x : ProjectiveSpace (Fin 2) (Spec ↧ℂ)) :
    IsDedekindDomain ((ProjectiveSpace (Fin 2) (Spec ↧ℂ)).presheaf.stalk x) := by
  letI := s0_complex_projective_integral 1
  let U := s0_complex_projective_cover 1
  obtain ⟨i, y, rfl⟩ := U.exists_eq x
  letI : Algebra (ULift.{0} ℤ) ℂ :=
    ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom).toAlgebra
  let J := {j : Fin 2 // j ≠ i}
  have hc : Fintype.card J = 1 := by
    simp [J, Fintype.card_subtype_compl]
  letI : Unique J := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hc)
  let R := MvPolynomial J ℂ
  let eR : R ≃+* Polynomial ℂ := (MvPolynomial.uniqueAlgEquiv ℂ J).toRingEquiv
  letI : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective eR.symm eR.symm.surjective
  let e : U.X i ≅ Spec ↧R :=
    (pullback.congrHom rfl (Subsingleton.elim _ _)) ≪≫ s0_projective_chart_fiber_iso ℂ i
  let a := (asIso ((U.f i).stalkMap y)).commRingCatIsoToRingEquiv
  let b := (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
  let c := (Spec.stalkIso ↧R (e.hom y)).commRingCatIsoToRingEquiv
  let E := (a.trans b.symm).trans c
  letI : IsPrincipalIdealRing ((ProjectiveSpace (Fin 2) (Spec ↧ℂ)).presheaf.stalk (U.f i y)) :=
    IsPrincipalIdealRing.of_surjective E.symm E.symm.surjective
  infer_instance

#print axioms s0_projective_line_stalk_dedekind
end HodgeLean.Foundations.Program
