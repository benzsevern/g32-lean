import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineIdealInclusion
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap

/-! # The affine ideal comparison on global sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- The natural affine comparison sends the value of an ideal section through the ring map. -/
lemma affineIdealPushforwardMap_value
    (R A S B : CommRingCat.{0}) (p : R ⟶ A) (q : S ⟶ B) (f : R ⟶ S) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫ Spec.map f)
    (x : (moduleSpecΓFunctor (R := R)).obj (idealModule (Spec.map p))) :
    (s2e_affine_ideal_sections_equiv S B q
      (((s2e_affine_pushforward_sections_iso R S f).hom.app (idealModule (Spec.map q)))
        (((moduleSpecΓFunctor (R := R)).map
          (idealPushforwardMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h)) x))).val =
      f (s2e_affine_ideal_sections_equiv R A p x).val := by
  change (Scheme.ΓSpecIso S).hom
      (s2e_idealModule_sections_equiv (Spec.map q) ⊤
        ((idealPushforwardMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h).val.app
          (op ⊤) x)).val =
    f ((Scheme.ΓSpecIso R).hom (s2e_idealModule_sections_equiv (Spec.map p) ⊤ x).val)
  rw [s2e_idealModule_sections_equiv_coe, s2e_idealModule_sections_equiv_coe]
  have hi := congrArg (fun t => t.val.app (op ⊤) x)
    (idealPushforwardMap_inclusion (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h)
  change (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map q).toRingCatSheafHom)).val.app
      (op ⊤) ((idealPushforwardMap (Spec.map p) (Spec.map q)
        (Spec.map f) (Spec.map k) h).val.app (op ⊤) x) =
    (Spec.map f).appTop
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map p).toRingCatSheafHom)).val.app
        (op ⊤) x) at hi
  rw [hi]
  exact congrArg (fun t : Γ(Spec R, ⊤) ⟶ S => t
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map p).toRingCatSheafHom)).val.app
      (op ⊤) x)) (Scheme.ΓSpecIso_naturality f)

/-- Transposition of the affine ideal identification is its section-kernel inverse. -/
lemma affineIdealIso_inv_transpose
    (R A : CommRingCat.{0}) (p : R ⟶ A) (N : (Spec R).Modules)
    (u : idealModule (Spec.map p) ⟶ N) :
    (tilde.adjunction (R := R)).homEquiv _ _ ((affineIdealIso R A p).inv ≫ u) =
      (s2e_affine_ideal_sections_equiv R A p).symm.toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := R)).map u := by
  rw [Adjunction.homEquiv_naturality_right]
  change (tilde.adjunction (R := R)).homEquiv _ _
      (((tilde.adjunction (R := R)).homEquiv _ _).symm
        (s2e_affine_ideal_sections_equiv R A p).symm.toModuleIso.hom) ≫ _ = _
  rw [Equiv.apply_symm_apply]

end AlgebraicGeometry.Conormal
