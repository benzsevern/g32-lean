import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEvaluation

/-! # Linearity of the actual native dual evaluation map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- A scalar relation between the original sections is retained by actual
native dual evaluation on every original open. -/
theorem paired_c3_evaluation_at_smul {X : Scheme.{0}} (L : X.Modules)
    (s t : Γ(L, ⊤)) (U : X.Opens) (c : Γ(X, U))
    (h : c • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    (φ : Γ(L.dual, U)) :
    (pairedC3EvaluationAtSection L t).app U φ =
      c • (pairedC3EvaluationAtSection L s).app U φ := by
  let ψ : Γ(pairedC3HomSheaf L (SheafOfModules.unit X.ringCatSheaf), U) :=
    (pairedC3DualPresheafIso L).hom.val.app (op U) φ
  let f : Γ(L, U) →ₗ[Γ(X, U)] Γ(SheafOfModules.unit X.ringCatSheaf, U) :=
    ψ.1 (𝟙 (op U))
  change f (L.presheaf.map (homOfLE le_top).op t) =
    c • f (L.presheaf.map (homOfLE le_top).op s)
  exact (congrArg f h).symm.trans (f.map_smul _ _)

#print axioms paired_c3_evaluation_at_smul
end HodgeLean.Foundations.Program.G32Native
