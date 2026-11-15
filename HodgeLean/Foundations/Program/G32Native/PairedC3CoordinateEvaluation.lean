import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # Evaluation of the actual negative line on a coordinate section -/
noncomputable section
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Evaluation on a specified global section, before the native dual
comparison, retaining all natural restriction maps. -/
def pairedC3HomEvaluation {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) :
    pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf where
  val := {
    app U := by
      change ModuleCat.of (Γ(X, U.unop))
        (Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U.unop)) ⟶
          ModuleCat.of (Γ(X, U.unop)) (Γ(X, U.unop))
      exact ModuleCat.ofHom (pairedC3FrameEvaluation
        (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s))
    naturality := by
      intro U V f
      ext φ
      have hs : M.presheaf.map f
          (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s) =
            M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op s := by
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl
      change pairedC3FrameEvaluation _
          ((pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf)).presheaf.map f φ) = _
      rw [← hs]
      exact paired_c3_dual_evaluation_restrict f.unop.le _ φ }

/-- The actual native dual evaluates on the specified global section. -/
def pairedC3EvaluationAtSection {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) :
    M.dual ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (pairedC3DualPresheafIso M).hom ≫ pairedC3HomEvaluation M s

/-- Multiplication by the specified homogeneous coordinate, on the actual
negative line and into the original structure module. -/
def pairedC3CoordinateEvaluation (k : ℕ) (j : Fin (k + 1)) :
    pairedC3NegativeLine k ⟶ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf :=
  pairedC3EvaluationAtSection (X := pairedC3Proj k) (ProjSpace.twistingSheaf ℂ k)
    (ProjSpace.twistingCoordinateSection ℂ k j)

/-- Evaluation on an actual local frame is bijective before specializing
its underlying module to a glued projective twisting line. -/
theorem paired_c3_evaluation_at_frame_bijective {X : Scheme.{0}} (M : X.Modules)
    (s : Γ(M, ⊤)) (U : X.Opens)
    (hs : IsFrameOn (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) U) :
    Function.Bijective ((pairedC3EvaluationAtSection M s).app U) := by
  change Function.Bijective (pairedC3NativeDualFrameEquiv hs)
  exact (pairedC3NativeDualFrameEquiv hs).bijective

/-- Away from the specified coordinate hyperplane, its evaluation map
is bijective on every smaller open, through the actual dual-frame coordinates. -/
theorem paired_c3_coordinate_evaluation_bijective (k : ℕ) (j : Fin (k + 1))
    (U : (pairedC3Proj k).Opens) (hU : U ≤ ProjSpace.standardOpen ℂ k j) :
    Function.Bijective ((pairedC3CoordinateEvaluation k j).app U) := by
  let hs := ((ProjSpace.isFrameOn_twistingCoordinateSection ℂ k j).map
    (homOfLE (le_top : U ≤ ⊤))).mono hU
  exact paired_c3_evaluation_at_frame_bijective _ _ _ hs

#print axioms paired_c3_evaluation_at_frame_bijective
#print axioms paired_c3_coordinate_evaluation_bijective
#print axioms pairedC3EvaluationAtSection
#print axioms pairedC3CoordinateEvaluation
#print axioms pairedC3HomEvaluation
end HodgeLean.Foundations.Program.G32Native
