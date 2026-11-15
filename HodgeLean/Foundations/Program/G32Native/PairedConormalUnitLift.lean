import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalLift
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Submodules.FiniteSectionSubmodule

/-! # Lifting arrows from the actual structure module -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {X : Scheme}

/-- A compatible section family is determined by its value on the whole space. -/
theorem conormal_sections_top_injective (M : X.Modules) :
    Function.Injective (fun s : M.sections => s.val (op ⊤)) := by
  intro s t h
  apply Subtype.ext
  funext U
  rw [← s.property U.unop.leTop.op, ← t.property U.unop.leTop.op]
  exact congrArg (fun x => M.val.map U.unop.leTop.op x) h

/-- Surjectivity on actual global sections lifts every arrow from the unit sheaf. -/
theorem conormal_unit_lift_of_top_surjective {M N : X.Modules} (g : M ⟶ N)
    (hg : Function.Surjective (g.app ⊤))
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    ∃ l : SheafOfModules.unit X.ringCatSheaf ⟶ M, l ≫ g = u := by
  obtain ⟨y, hy⟩ := hg ((N.unitHomEquiv u).val (op ⊤))
  refine ⟨M.unitHomEquiv.symm (M.topSection y), ?_⟩
  apply N.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  apply conormal_sections_top_injective N
  change g.app ⊤ ((M.topSection y).val (op ⊤)) = _
  rw [SheafOfModules.topSection_top]
  exact hy

end HodgeLean.Foundations.Program.G32Native
