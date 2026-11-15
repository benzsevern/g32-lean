import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Local freeness from actual scheme-open frames -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Frames on scheme opens around every point give local freeness on the
original ringed site. The index sets may vary from point to point. -/
theorem paired_module_locallyFree_of_localFrames {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ I : Type,
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)) :
    M.IsLocallyFree := by
  classical
  choose U hU I he using h
  let e x := Classical.choice (he x)
  let q : M.LocalGeneratorsData := {
    I := X
    X := U
    coversTop V x hx := ⟨V ⊓ U x, homOfLE inf_le_left,
      ⟨x, ⟨homOfLE inf_le_right⟩⟩, hx, hU x⟩
    generators x := (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (e x).hom }
  have : q.IsLocallyFreeData := by
    constructor
    intro x
    change IsIso ((SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (e x).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (IsIso.id _) (Iso.isIso_hom _)
  exact q.isLocallyFree

end HodgeLean.Foundations.Program.G32Native
