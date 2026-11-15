import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import HodgeLean.Foundations.Program.SchoenTowerL1aOpenSectionLocalization

/-! # Actual parameter evaluation under section restriction

Implication from actual section pullback and principal localization to
preservation of the ordered and symmetric polynomial parameter maps.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Evaluation with the actual base section map commutes with actual section pullback.
Source: Hartshorne, Algebraic Geometry, II.2, section functoriality. -/
theorem s2v_l1a_section_parameter_comp
    {X Y : Over (Spec ↧ℂ)} (r : X ⟶ Y) {ι : Type} (z : ι → Γ(Y.left, ⊤)) :
    r.left.appTop.hom.comp (MvPolynomial.eval₂Hom Y.hom.appTop.hom z) =
      MvPolynomial.eval₂Hom X.hom.appTop.hom (fun i => r.left.appTop.hom (z i)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change r.left.appTop.hom ((MvPolynomial.eval₂Hom Y.hom.appTop.hom z)
      (MvPolynomial.C c)) = (MvPolynomial.eval₂Hom X.hom.appTop.hom
        (fun i => r.left.appTop.hom (z i))) (MvPolynomial.C c)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    have H := congrArg (fun f : X.left ⟶ Spec ↧ℂ => f.appTop.hom c) (Over.w r)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H
  · intro i
    change r.left.appTop.hom ((MvPolynomial.eval₂Hom Y.hom.appTop.hom z)
      (MvPolynomial.X i)) = (MvPolynomial.eval₂Hom X.hom.appTop.hom
        (fun i => r.left.appTop.hom (z i))) (MvPolynomial.X i)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

/-- A polynomial parameter map etale on the abstract principal localization
is etale on the actual restricted section ring with that localization map.
Source: Hartshorne, Algebraic Geometry, II.2 and III.10. -/
theorem s2v_l1a_etale_principal_section_parameters
    {X Y : Over (Spec ↧ℂ)} (r : X ⟶ Y) {ι : Type} (z : ι → Γ(Y.left, ⊤))
    (d : Γ(Y.left, ⊤))
    (hloc : letI := r.left.appTop.hom.toAlgebra
      IsLocalization.Away d Γ(X.left, ⊤))
    (hEt : ((algebraMap Γ(Y.left, ⊤) (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) z).toRingHom).Etale) :
    (MvPolynomial.eval₂Hom X.hom.appTop.hom (fun i => r.left.appTop.hom (z i))).Etale := by
  let D := Γ(Y.left, ⊤)
  let A := Γ(X.left, ⊤)
  letI : Algebra D A := r.left.appTop.hom.toAlgebra
  letI : IsLocalization.Away d A := hloc
  let e : Localization.Away d ≃ₐ[D] A :=
    IsLocalization.algEquiv (Submonoid.powers d) (Localization.Away d) A
  have H := RingHom.Etale.respectsIso.1 _ e.toRingEquiv hEt
  have heq₀ : e.toRingHom.comp ((algebraMap D (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) z).toRingHom) =
        r.left.appTop.hom.comp (MvPolynomial.aeval (R := ℂ) z).toRingHom := by
    apply RingHom.ext
    intro p
    exact e.commutes ((MvPolynomial.aeval (R := ℂ) z) p)
  have heq₁ : (s2t_overSectionsAlgHom r).comp (MvPolynomial.aeval (R := ℂ) z) =
      MvPolynomial.aeval (R := ℂ) (fun i => r.left.appTop.hom (z i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  have heq₂ : r.left.appTop.hom.comp (MvPolynomial.aeval (R := ℂ) z).toRingHom =
      (MvPolynomial.aeval (R := ℂ) (fun i => r.left.appTop.hom (z i))).toRingHom :=
    congrArg (fun f : MvPolynomial ι ℂ →ₐ[ℂ] A => f.toRingHom) heq₁
  rw [heq₀, heq₂] at H
  rw [s2v_l1a_structure_section_coefficients]
  exact s2v_l1a_etale_eval_change_coefficients _ _ _ H

end HodgeLean.Foundations.Program
