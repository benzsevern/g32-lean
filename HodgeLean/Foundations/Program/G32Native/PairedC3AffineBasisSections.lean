import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteFrameCoordinates
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Affine bases and synthesis over the original ring of global sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction to the same open preserves the original section. -/
theorem paired_c3_module_restrict_self {X : Scheme.{0}} (M : X.Modules)
    (V : X.Opens) (s : Γ(M, V)) : pairedC3ModuleRestrict M le_rfl s = s := by
  change M.presheaf.map (𝟙 _) s = s
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (Opposite.op V)) s

/-- A specified affine module basis gives bijective synthesis over the
original ring of global sections, through its canonical ring isomorphism. -/
theorem paired_c3_affine_basis_section_synthesis (R : CommRingCat.{0})
    (M : (Spec R).Modules) {σ : Type} [Fintype σ]
    (b : Module.Basis σ R ((moduleSpecΓFunctor (R := R)).obj M))
    (g : σ → Γ(M, ⊤)) (hb : ∀ a, b a = g a) :
    Function.Bijective (pairedC3FiniteFrameSynthesis g ⊤ le_top) := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have heq : (pairedC3FiniteFrameSynthesis g ⊤ le_top :
      (σ → Γ(Spec R, ⊤)) → Γ(M, ⊤)) =
      b.equivFun.symm ∘ (fun c a => e (c a)) := by
    funext c
    rw [Function.comp_apply, Module.Basis.equivFun_symm_apply]
    change (∑ a, c a • pairedC3ModuleRestrict M le_top (g a)) = _
    apply Finset.sum_congr rfl
    intro a _
    rw [paired_c3_module_restrict_self, hb a]
    change c a • g a = (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom (c a)) • g a
    rw [Iso.hom_inv_id_apply]
  rw [heq]
  exact b.equivFun.symm.bijective.comp
    (Equiv.piCongrRight (fun _ : σ => e.toEquiv)).bijective

#print axioms paired_c3_affine_basis_section_synthesis
end HodgeLean.Foundations.Program.G32Native
