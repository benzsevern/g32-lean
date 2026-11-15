import HodgeLean.Foundations.Program.G32Native.AffineIdealSectionKernel
import HodgeLean.Foundations.Program.G32Native.AffineOpenImmersionSections

/-! # Actual affine ideal sections and the original immersion kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine chart ideal sections identify with the kernel of the
original immersion section map, retaining their original ambient ring values. -/
def affineOpenIdealSectionKernelEquiv {Q W : Scheme.{0}} (i : Q ⟶ W)
    [IsClosedImmersion i] (U : W.Opens) (hU : IsAffineOpen U) :
    (moduleSpecΓFunctor (R := Γ(W, U))).obj
      (Conormal.idealModule ((i ∣_ U) ≫ hU.isoSpec.hom)) ≃ₗ[Γ(W, U)] RingHom.ker (i.app U).hom := by
  let R := Γ(W, U)
  let j := (i ∣_ U) ≫ hU.isoSpec.hom
  let e := affineIdealSectionKernelEquiv R j
  have he (r : R) : (i.app U) r = (i ⁻¹ᵁ U).topIso.hom
      (j.appTop ((Scheme.ΓSpecIso R).inv r)) := by
    exact (congrArg (fun f : R ⟶ Γ(Q, i ⁻¹ᵁ U) => f r)
      (affineOpenImmersion_sections i U hU)).symm
  let f := (affineIdealSectionInclusion R j).codRestrict (RingHom.ker (i.app U).hom) (by
    intro m
    rw [RingHom.mem_ker, he]
    change (i ⁻¹ᵁ U).topIso.hom
      ((j.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) (e m).val) = 0
    rw [(e m).property, map_zero])
  apply LinearEquiv.ofBijective f
  constructor
  · intro m n h
    apply e.injective
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    change affineIdealSectionInclusion R j m = affineIdealSectionInclusion R j n at hv
    change affineIdealSectionInclusion R j m = affineIdealSectionInclusion R j n
    exact hv
  · intro r
    have hr : j.appTop ((Scheme.ΓSpecIso R).inv r.val) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U).topIso.hom).injective
      rw [map_zero, ← he]
      exact r.property
    refine ⟨e.symm ⟨r.val, hr⟩, ?_⟩
    apply Subtype.ext
    change (e (e.symm ⟨r.val, hr⟩)).val = r.val
    rw [e.apply_symm_apply]

#print axioms affineOpenIdealSectionKernelEquiv
end HodgeLean.Foundations.Program.G32Native
