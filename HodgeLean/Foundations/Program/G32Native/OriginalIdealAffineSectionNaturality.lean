import HodgeLean.Foundations.Program.G32Native.ConormalIdealSectionNaturality
import HodgeLean.Foundations.Program.G32Native.IdealEquationAffineTransport

/-! # Original ideal sections in the specified affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution
open HodgeLean.Foundations.Algebraic

/-- The affine equation section includes as multiplication by the same equation. -/
theorem affineIdealModuleSection_inclusion_scalar
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom) :
    affineIdealModuleSection R S φ u ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom) =
      f5sheaf_scal ((Scheme.ΓSpecIso R).inv u.val) :=
  idealSection_inclusion_eq_scalar _ _ _ (affineIdealModuleSection_inclusion_top R S φ u)

/-- The original equation in the inverse affine coordinates is its spectrum section. -/
theorem originalIdealOpenSection_affine_scalar
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens) (hA : IsAffineOpen A)
    (u : RingHom.ker (j.app A).hom) :
    hA.isoSpec.inv.appTop (A.topIso.inv u.val) =
      (Scheme.ΓSpecIso (W.presheaf.obj (.op A))).inv u.val := by
  rw [IsAffineOpen.isoSpec_inv_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The ideal section in the affine chart is fixed by its original equation,
 including its sign and coefficient. -/
theorem originalIdealAffineSection_scalar_unique
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens)
    (u : RingHom.ker (j.app A).hom)
    (t : SheafOfModules.unit (Spec (W.presheaf.obj (.op A))).ringCatSheaf ⟶
      Conormal.idealModule (Spec.map (j.app A)))
    (ht : t ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (Spec.map (j.app A)).toRingCatSheafHom) =
        f5sheaf_scal ((Scheme.ΓSpecIso (W.presheaf.obj (.op A))).inv u.val)) :
    t = affineIdealModuleSection (W.presheaf.obj (.op A))
      (Q.presheaf.obj (.op (j ⁻¹ᵁ A))) (j.app A) u := by
  apply idealSection_ext (Spec.map (j.app A))
  exact ht.trans (affineIdealModuleSection_inclusion_scalar _ _ _ u).symm

end HodgeLean.Foundations.TubularEuler
