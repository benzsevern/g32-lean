import HodgeLean.Foundations.Program.SchoenCycleC2IdealLocalizationHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The affine section comparison identifies the actual sheaf restriction
with principal-open restriction on the same kernel ideal data. -/
theorem s2e_idealModule_basicOpen_restriction
    {K B : Scheme.{0}} (k : K ⟶ B) [QuasiCompact k]
    (U : B.affineOpens) (f : Γ(B, U)) (x : Γ(s2c_idealModule k, U)) :
    s2e_idealModule_affine_sections_equiv k (B.affineBasicOpen f)
      ((s2c_idealModule k).val.map (homOfLE (B.basicOpen_le f)).op x) =
      s2e_ideal_basicOpen_linear B k.ker U f
        (s2e_idealModule_affine_sections_equiv k U x) := by
  apply Subtype.ext
  change (s2e_idealModule_sections_equiv k (B.basicOpen f)
      ((s2c_idealModule k).val.map (homOfLE (B.basicOpen_le f)).op x) :
        Γ(B, B.basicOpen f)) =
      B.presheaf.map (homOfLE (B.basicOpen_le f)).op
        (s2e_idealModule_sections_equiv k U x)
  exact s2e_idealModule_sections_equiv_restrict k (B.basicOpen_le f) x

/-- Actual ideal-module sections localize under restriction from an affine
open to one of its principal opens. -/
theorem s2e_idealModule_basicOpen_isLocalized
    {K B : Scheme.{0}} (k : K ⟶ B) [QuasiCompact k]
    (U : B.affineOpens) (f : Γ(B, U)) :
    IsLocalizedModule.Away f
      ((s2c_idealModule k).val.map (homOfLE (B.basicOpen_le f)).op).hom := by
  letI : Module Γ(B, B.basicOpen f) Γ(s2c_idealModule k, B.affineBasicOpen f) :=
    ((s2c_idealModule k).val.obj (op (B.basicOpen f))).isModule
  letI : Module Γ(B, U) Γ(s2c_idealModule k, B.affineBasicOpen f) :=
    Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
  letI : Module Γ(B, U) (k.ker.ideal (B.affineBasicOpen f)) :=
    Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
  let : IsScalarTower Γ(B, U) Γ(B, B.basicOpen f) Γ(s2c_idealModule k, B.affineBasicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower Γ(B, U) Γ(B, B.basicOpen f)
      (k.ker.ideal (B.affineBasicOpen f)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eU := s2e_idealModule_affine_sections_equiv k U
  let eV : Γ(s2c_idealModule k, B.affineBasicOpen f) ≃ₗ[Γ(B, U)]
      k.ker.ideal (B.affineBasicOpen f) :=
    { __ := (s2e_idealModule_affine_sections_equiv k (B.affineBasicOpen f)).toAddEquiv
      map_smul' := fun r x =>
        (s2e_idealModule_affine_sections_equiv k (B.affineBasicOpen f)).map_smul
          ((B.presheaf.map (homOfLE (B.basicOpen_le f)).op).hom r) x }
  let g := s2e_ideal_basicOpen_linear B k.ker U f
  let : IsLocalizedModule.Away f g := s2e_ideal_basicOpen_isLocalized B k.ker U f
  let : IsLocalizedModule.Away f (eV.symm.toLinearMap ∘ₗ g) :=
    IsLocalizedModule.of_linearEquiv (.powers f) g eV.symm
  have h := IsLocalizedModule.of_linearEquiv_right (.powers f)
    (eV.symm.toLinearMap ∘ₗ g) eU
  have heq : ((s2c_idealModule k).val.map (homOfLE (B.basicOpen_le f)).op).hom =
      eV.symm.toLinearMap ∘ₗ g ∘ₗ eU.toLinearMap := by
    ext x
    apply eV.injective
    change eV (((s2c_idealModule k).val.map (homOfLE (B.basicOpen_le f)).op).hom x) =
      eV (eV.symm (g (eU x)))
    rw [LinearEquiv.apply_symm_apply]
    exact s2e_idealModule_basicOpen_restriction k U f x
  rw [heq]
  exact h

end HodgeLean.Foundations.Program
