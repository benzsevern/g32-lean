import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual affine ideal sections map to the kernel of the defining
ring homomorphism through the canonical global-section identification. -/
def s2e_affine_ideal_sections_to_kernel
    (R S : CommRingCat.{0}) (φ : R ⟶ S) :
    Γ(s2c_idealModule (Spec.map φ), ⊤) →ₗ[R] RingHom.ker φ.hom := by
  let e := s2e_idealModule_sections_equiv (Spec.map φ) ⊤
  refine
    { toFun := fun x => ⟨(Scheme.ΓSpecIso R).hom (e x).val, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · change φ ((Scheme.ΓSpecIso R).hom (e x).val) = 0
    have ha : (Spec.map φ).appTop (e x).val = 0 := (e x).property
    have hc := congrArg (fun ψ : Γ(Spec R, ⊤) ⟶ S => ψ (e x).val)
      (Scheme.ΓSpecIso_naturality φ)
    change (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop (e x).val) =
      φ ((Scheme.ΓSpecIso R).hom (e x).val) at hc
    rw [← hc, ha, map_zero]
  · intro x y
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  · intro r x
    apply Subtype.ext
    change (Scheme.ΓSpecIso R).hom ((e ((Scheme.ΓSpecIso R).inv r • x)).val) =
      r * (Scheme.ΓSpecIso R).hom (e x).val
    simp only [map_smul, SetLike.val_smul, smul_eq_mul, map_mul, Iso.inv_hom_id_apply]

/-- The actual affine ideal sections are linearly equivalent to the
kernel of the same defining ring homomorphism. -/
def s2e_affine_ideal_sections_equiv
    (R S : CommRingCat.{0}) (φ : R ⟶ S) :
    Γ(s2c_idealModule (Spec.map φ), ⊤) ≃ₗ[R] RingHom.ker φ.hom := by
  let e := s2e_idealModule_sections_equiv (Spec.map φ) ⊤
  apply LinearEquiv.ofBijective (s2e_affine_ideal_sections_to_kernel R S φ)
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).injective
    exact congrArg Subtype.val hxy
  · intro y
    let a : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv y.val
    have ha : (Spec.map φ).appTop a = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).injective
      have hc := congrArg (fun ψ : Γ(Spec R, ⊤) ⟶ S => ψ a)
        (Scheme.ΓSpecIso_naturality φ)
      change (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop a) =
        φ ((Scheme.ΓSpecIso R).hom a) at hc
      have hy : φ y.val = 0 := y.property
      simpa only [map_zero, a, Iso.inv_hom_id_apply, hy] using hc
    let z : RingHom.ker ((Spec.map φ).app ⊤).hom := ⟨a, ha⟩
    refine ⟨e.symm z, ?_⟩
    apply Subtype.ext
    change (Scheme.ΓSpecIso R).hom (e (e.symm z)).val = y.val
    rw [e.apply_symm_apply]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso R) y.val

end HodgeLean.Foundations.Program
