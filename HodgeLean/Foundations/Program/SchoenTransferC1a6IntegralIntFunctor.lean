import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralCoefficients

/-! The canonical integral module underlying a complex module. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

def s4_c1a6_intLinear {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := map_add f
  map_smul' n x := by
    convert! AddMonoidHom.map_zsmul f n x <;> ext <;> apply int_smul_eq_zsmul

def s4_c1a6_forgetComplexToInt : ModuleCat.{0} ℂ ⥤ ModuleCat.{0} ℤ where
  obj M := ModuleCat.of ℤ M
  map f := ModuleCat.ofHom f.hom.toAddMonoidHom.toIntLinearMap

def s4_c1a6_forgetComplexToIntIso :
    s4_c1a6_forgetComplexToInt ≅ ModuleCat.restrictScalars (algebraMap ℤ ℂ) :=
  NatIso.ofComponents (fun M =>
    { hom := ModuleCat.ofHom (X := s4_c1a6_forgetComplexToInt.obj M)
        (Y := (ModuleCat.restrictScalars (algebraMap ℤ ℂ)).obj M)
        (s4_c1a6_intLinear (AddMonoidHom.id M))
      inv := ModuleCat.ofHom (X := (ModuleCat.restrictScalars (algebraMap ℤ ℂ)).obj M)
        (Y := s4_c1a6_forgetComplexToInt.obj M)
        (s4_c1a6_intLinear (AddMonoidHom.id M))
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }) (by intro M N f; ext x; rfl)

instance : PreservesLimits s4_c1a6_forgetComplexToInt :=
  preservesLimits_of_natIso s4_c1a6_forgetComplexToIntIso.symm
instance : PreservesColimits s4_c1a6_forgetComplexToInt :=
  preservesColimits_of_natIso s4_c1a6_forgetComplexToIntIso.symm

end HodgeLean.Foundations.Program
