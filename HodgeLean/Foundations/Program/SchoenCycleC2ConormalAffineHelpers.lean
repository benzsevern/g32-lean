import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On actual affine schemes the kernel-defined conormal sheaf is the
associated sheaf of the scalar-extended actual ideal sections. -/
def s2e_affine_conormal_sections_iso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) :
    s2c_conormal (Spec.map φ) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := R)).obj (s2c_idealModule (Spec.map φ)))) := by
  let M := s2c_idealModule (Spec.map φ)
  let : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  exact ((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ)).symm ≪≫
    (s2e_affine_pullback_tilde_iso R S φ).app ((moduleSpecΓFunctor (R := R)).obj M)

end HodgeLean.Foundations.Program
