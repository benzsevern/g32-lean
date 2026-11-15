import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Original global module sections as structure-module morphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original global module section as its actual compatible family
of restrictions on every ambient open. -/
def moduleGlobalSection {X : Scheme.{0}} (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op m)
    (fun U V f => by
      change M.val.map f
        (M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op m) =
        M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op m
      rw [← M.val.map_comp_apply]
      rfl)

/-- The structure-module morphism of an original global module section,
using its actual restrictions on every open. -/
def moduleGlobalSectionHom {X : Scheme.{0}} (M : X.Modules) (m : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (moduleGlobalSection M m)

/-- The original structure-module morphism retains the original global
section when evaluated on one at the top open. -/
theorem moduleGlobalSectionHom_top {X : Scheme.{0}} (M : X.Modules) (m : Γ(M, ⊤)) :
    (moduleGlobalSectionHom M m).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = m := by
  have h := congrArg (fun s : M.sections => s.val (Opposite.op ⊤))
    (M.unitHomEquiv.apply_symm_apply (moduleGlobalSection M m))
  change (moduleGlobalSectionHom M m).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) =
    M.val.map (𝟙 (Opposite.op (⊤ : X.Opens))) m at h
  rw [M.val.map_id] at h
  exact h

#print axioms moduleGlobalSectionHom_top
#print axioms moduleGlobalSectionHom
#print axioms moduleGlobalSection
end HodgeLean.Foundations.Program.G32Native
