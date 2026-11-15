import HodgeLean.Foundations.TubularEuler.AffineConormalSectionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers
import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs

/-! # The actual affine ideal inclusion in original ring coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual kernel ideal inclusion on affine global sections, transported
through the canonical affine ring identification. -/
def affineIdealSectionInclusion (R : CommRingCat.{0}) {Q : Scheme.{0}} (i : Q ⟶ Spec R) :
    (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule i) →ₗ[R] R := by
  let e := s2e_idealModule_sections_equiv i ⊤
  refine {
    toFun := fun m => (Scheme.ΓSpecIso R).hom (e m).val
    map_add' := ?_
    map_smul' := ?_ }
  · intro m n
    simp only [map_add, Submodule.coe_add]
  · intro r m
    change (Scheme.ΓSpecIso R).hom ((e ((Scheme.ΓSpecIso R).inv r •
      (show Γ(Conormal.idealModule i, ⊤) from m))).val) =
      r * (Scheme.ΓSpecIso R).hom (e m).val
    simp only [map_smul, SetLike.val_smul, smul_eq_mul, map_mul, Iso.inv_hom_id_apply]

/-- Every original ideal section evaluates to zero at any affine point
factoring through the defining morphism. -/
theorem affineIdealSectionInclusion_map_zero (R S : CommRingCat.{0}) (ε : R ⟶ S)
    {Q : Scheme.{0}} (i : Q ⟶ Spec R) (x : Spec S ⟶ Q)
    (hx : x ≫ i = Spec.map ε)
    (m : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule i)) :
    ε (affineIdealSectionInclusion R i m) = 0 := by
  let e := s2e_idealModule_sections_equiv i ⊤
  have hm : i.appTop (e m).val = 0 := (e m).property
  have hn := congrArg (fun f : Γ(Spec R, ⊤) ⟶ S => f (e m).val)
    (Scheme.ΓSpecIso_naturality ε)
  change (Scheme.ΓSpecIso S).hom ((Spec.map ε).appTop (e m).val) =
    ε ((Scheme.ΓSpecIso R).hom (e m).val) at hn
  change ε ((Scheme.ΓSpecIso R).hom (e m).val) = 0
  rw [← hn, ← hx, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hm, map_zero, map_zero]

#print axioms affineIdealSectionInclusion_map_zero
#print axioms affineIdealSectionInclusion
end HodgeLean.Foundations.Program.G32Native


/-! # Original affine ideal sections retain their structure-sheaf inclusions -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

/-- The affine kernel coordinate of an ideal section is its actual
structure-sheaf value in the canonical spectrum coordinates.
Source: `s2e_affine_ideal_sections_equiv` and
`s2e_idealModule_sections_equiv_coe`. -/
theorem affineIdealSections_equiv_coe
    (R S : CommRingCat.{0}) (φ : R ⟶ S)
    (s : Γ(Conormal.idealModule (Spec.map φ), ⊤)) :
    ((s2e_affine_ideal_sections_equiv R S φ) s).val =
      (Scheme.ΓSpecIso R).hom
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (Spec.map φ).toRingCatSheafHom)).val.app (.op ⊤) s) := by
  change (Scheme.ΓSpecIso R).hom
      ((s2e_idealModule_sections_equiv (Spec.map φ) ⊤) s).val = _
  rw [s2e_idealModule_sections_equiv_coe]

/-- The section descended from the original equation includes into the
structure module as that same equation.
Source: `affineIdealModuleSection_top` and `affineIdealSections_equiv_coe`. -/
theorem affineIdealModuleSection_inclusion_top
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (Spec.map φ).toRingCatSheafHom)).val.app (.op ⊤)
        ((affineIdealModuleSection R S φ u).val.app (.op ⊤) (1 : Γ(Spec R, ⊤))) =
      (Scheme.ΓSpecIso R).inv u.val := by
  rw [affineIdealModuleSection_top]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).injective
  rw [Iso.inv_hom_id_apply]
  exact (affineIdealSections_equiv_coe R S φ
    ((s2e_affine_ideal_sections_equiv R S φ).symm u)).symm.trans
      (congrArg Subtype.val ((s2e_affine_ideal_sections_equiv R S φ).apply_symm_apply u))

#print axioms affineIdealSections_equiv_coe
#print axioms affineIdealModuleSection_inclusion_top
end HodgeLean.Foundations.TubularEuler
