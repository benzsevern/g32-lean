import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers
import Mathlib.RingTheory.Localization.Algebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The linear restriction of actual ideal data to a principal affine open. -/
def s2e_ideal_basicOpen_linear
    (B : Scheme.{0}) (I : B.IdealSheafData) (U : B.affineOpens) (f : Γ(B, U)) :
    letI : Module Γ(B, U) (I.ideal (B.affineBasicOpen f)) :=
      Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
    I.ideal U →ₗ[Γ(B, U)] I.ideal (B.affineBasicOpen f) := by
  letI : Module Γ(B, U) (I.ideal (B.affineBasicOpen f)) :=
    Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
  let ρ := (B.presheaf.map (homOfLE (B.basicOpen_le f)).op).hom
  refine
    { toFun := fun x => ⟨ρ x, ?_⟩
      map_add' := fun x y => Subtype.ext (map_add ρ (x : Γ(B, U)) (y : Γ(B, U)))
      map_smul' := ?_ }
  · rw [← I.map_ideal_basicOpen U f]
    exact Ideal.mem_map_of_mem _ x.property
  · intro r x
    apply Subtype.ext
    change ρ (r * x.val) = ρ r * ρ x.val
    exact map_mul ρ r x.val

/-- The actual principal-open ideal restriction is module localization. -/
theorem s2e_ideal_basicOpen_isLocalized
    (B : Scheme.{0}) (I : B.IdealSheafData) (U : B.affineOpens) (f : Γ(B, U)) :
    letI : Module Γ(B, U) (I.ideal (B.affineBasicOpen f)) :=
      Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
    IsLocalizedModule.Away f (s2e_ideal_basicOpen_linear B I U f) := by
  letI : Module Γ(B, U) (I.ideal (B.affineBasicOpen f)) :=
    Module.compHom _ (algebraMap Γ(B, U) Γ(B, B.basicOpen f))
  let : IsScalarTower Γ(B, U) Γ(B, B.basicOpen f) (I.ideal (B.affineBasicOpen f)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalization.Away f Γ(B, B.basicOpen f) := U.2.isLocalization_basicOpen f
  let e := (LinearEquiv.ofEq _ _ (I.map_ideal_basicOpen U f)).restrictScalars Γ(B, U)
  let : IsLocalizedModule.Away f
      (Algebra.idealMap Γ(B, B.basicOpen f) (I.ideal U)) :=
    Algebra.idealMap_isLocalizedModule (S := Γ(B, B.basicOpen f))
      (M := Submonoid.powers f) (I.ideal U)
  have h : IsLocalizedModule.Away f
      (e.toLinearMap ∘ₗ Algebra.idealMap Γ(B, B.basicOpen f) (I.ideal U)) :=
    IsLocalizedModule.of_linearEquiv (.powers f) _ e
  have heq : s2e_ideal_basicOpen_linear B I U f =
      e.toLinearMap ∘ₗ Algebra.idealMap Γ(B, B.basicOpen f) (I.ideal U) := by
    ext x
    rfl
  rw [heq]
  exact h

end HodgeLean.Foundations.Program
