import HodgeLean.Foundations.Program.G32Native.AffineIdealSectionInclusion

/-! # The actual affine ideal sections and their original ring kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual ideal-module sections in affine ring coordinates identify with
the kernel of the original global section map. -/
def affineIdealSectionKernelEquiv (R : CommRingCat.{0}) {Q : Scheme.{0}}
    (i : Q ⟶ Spec R) :
    let ψ := i.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule i) ≃ₗ[R] RingHom.ker ψ := by
  let ψ := i.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let e := s2e_idealModule_sections_equiv i ⊤
  let f : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule i) →ₗ[R] RingHom.ker ψ :=
    (affineIdealSectionInclusion R i).codRestrict (RingHom.ker ψ) (by
      intro m
      change i.appTop ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom (e m).val)) = 0
      rw [Iso.hom_inv_id_apply]
      exact (e m).property)
  apply LinearEquiv.ofBijective f
  constructor
  · intro m n h
    apply e.injective
    apply Subtype.ext
    apply ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv).injective
    exact congrArg Subtype.val h
  · intro r
    let m := e.symm ⟨(Scheme.ΓSpecIso R).inv r.val, r.property⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change (Scheme.ΓSpecIso R).hom (e m).val = r.val
    rw [show e m = ⟨(Scheme.ΓSpecIso R).inv r.val, r.property⟩ from e.apply_symm_apply _]
    exact Iso.inv_hom_id_apply _ _

#print axioms affineIdealSectionKernelEquiv
end HodgeLean.Foundations.Program.G32Native
