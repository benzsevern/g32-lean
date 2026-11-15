import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleLocalizationHelpers
import Mathlib.AlgebraicGeometry.Modules.Tilde

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The actual ideal module of a quasi-compact morphism to an affine scheme
has the localization property on the standard principal-open basis. -/
theorem s2e_idealModule_spec_isLocalizing
    (R : CommRingCat.{0}) {K : Scheme.{0}} (k : K ⟶ Spec R) [QuasiCompact k] :
    IsLocalizing (modulesSpecToSheaf.obj (s2c_idealModule k)) := by
  intro f
  let g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv f
  let U : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let M := s2c_idealModule k
  letI : Module Γ(Spec R, ⊤) Γ(M, (Spec R).basicOpen g) :=
    Module.compHom _ (algebraMap Γ(Spec R, ⊤) Γ(Spec R, (Spec R).basicOpen g))
  let : IsScalarTower R Γ(Spec R, ⊤) Γ(M, (Spec R).basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let l : Γ(M, ⊤) →ₗ[Γ(Spec R, ⊤)] Γ(M, (Spec R).basicOpen g) :=
    (M.val.map (homOfLE ((Spec R).basicOpen_le g)).op).hom
  let : IsLocalizedModule.Away g l := s2e_idealModule_basicOpen_isLocalized k U g
  let : IsLocalizedModule.Away (algebraMap R Γ(Spec R, ⊤) f) l := by
    change IsLocalizedModule.Away g l
    infer_instance
  have h := IsLocalizedModule.restrictScalars_powers (A := Γ(Spec R, ⊤)) f l
  rw [← basicOpen_eq_of_affine f]
  exact h

/-- The canonical associated-module comparison for the actual ideal
module on an affine scheme is invertible. -/
theorem s2e_idealModule_spec_fromTilde_isIso
    (R : CommRingCat.{0}) {K : Scheme.{0}} (k : K ⟶ Spec R) [QuasiCompact k] :
    IsIso (s2c_idealModule k).fromTildeΓ := by
  exact (isIso_fromTildeΓ_iff_isLocalizing (s2c_idealModule k)).mpr
    (s2e_idealModule_spec_isLocalizing R k)

end HodgeLean.Foundations.Program
