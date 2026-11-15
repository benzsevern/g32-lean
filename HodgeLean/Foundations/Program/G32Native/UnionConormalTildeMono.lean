import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Associated sheaves retain injective module maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Injectivity of a module map is retained on all sections of its associated sheaf. -/
theorem union_tilde_map_sections_injective {R : CommRingCat} {M N : ModuleCat R}
    (f : M ⟶ N) (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective ((tilde.map f).val.app (Opposite.op U)) := by
  intro x y hxy
  apply Subtype.ext
  funext p
  apply IsLocalizedModule.map_injective p.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun s => s.val p) hxy

/-- Associated sheaves preserve a module monomorphism. -/
theorem union_tilde_map_mono {R : CommRingCat} {M N : ModuleCat R}
    (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  exact union_tilde_map_sections_injective f ((ModuleCat.mono_iff_injective f).mp
    inferInstance) U.unop

#print axioms union_tilde_map_sections_injective
#print axioms union_tilde_map_mono

end HodgeLean.Foundations.Program.G32Native
