import HodgeLean.Foundations.Program.G32Native.PairedC3DualGeneratorTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3FrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison

/-! # Negative-line coefficients on original common subopens -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Scalar coordinate in the specified dual generator on an original subopen. -/
def pairedC3NegativeLineCoordinate (k : ℕ) (i : Fin (k + 1))
    (V : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i) :
    Γ(pairedC3NegativeLine k, V) ≃ₗ[Γ(pairedC3Proj k, V)] Γ(pairedC3Proj k, V) :=
  (pairedC3FrameEquiv (paired_c3_coordinate_dual_generator_frame k i) hi hi).symm

/-- Negative-line coordinates retain the original section restrictions. -/
theorem paired_c3_negative_line_coordinate_restrict (k : ℕ) (i : Fin (k + 1))
    (V W : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i)
    (h : W ≤ V) (s : Γ(pairedC3NegativeLine k, V)) :
    pairedC3NegativeLineCoordinate k i W (h.trans hi)
      (pairedC3ModuleRestrict (pairedC3NegativeLine k) h s) =
      (pairedC3Proj k).presheaf.map (homOfLE h).op
        (pairedC3NegativeLineCoordinate k i V hi s) :=
  paired_c3_frame_coordinate_restrict
    (paired_c3_coordinate_dual_generator_frame k i) hi hi h s

/-- The original dual-generator ratio identity holds on every common subopen. -/
theorem paired_c3_dual_generator_transition_subopen (k : ℕ) (i j : Fin (k + 1))
    (V : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i)
    (hj : V ≤ ProjSpace.standardOpen ℂ k j) :
    pairedC3ModuleRestrict (pairedC3NegativeLine k) hi (pairedC3CoordinateDualGenerator k i) =
      (pairedC3Proj k).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ k i j) •
      pairedC3ModuleRestrict (pairedC3NegativeLine k) hj (pairedC3CoordinateDualGenerator k j) := by
  have h := congrArg (pairedC3ModuleRestrict (pairedC3NegativeLine k) (le_inf hi hj))
    (paired_c3_coordinate_dual_generator_transition k i j)
  dsimp only [pairedC3ModuleRestrict] at h ⊢
  rw [Scheme.Modules.map_smul] at h
  simpa only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using h

/-- Coefficients change by X_j/X_i, with the original index order. -/
theorem paired_c3_negative_line_coordinate_transition (k : ℕ) (i j : Fin (k + 1))
    (V : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i)
    (hj : V ≤ ProjSpace.standardOpen ℂ k j) (s : Γ(pairedC3NegativeLine k, V)) :
    pairedC3NegativeLineCoordinate k j V hj s =
      (pairedC3Proj k).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ k i j) *
      pairedC3NegativeLineCoordinate k i V hi s := by
  apply (pairedC3FrameEquiv (paired_c3_coordinate_dual_generator_frame k j) hj hj).injective
  change (pairedC3FrameEquiv (paired_c3_coordinate_dual_generator_frame k j) hj hj)
    ((pairedC3FrameEquiv (paired_c3_coordinate_dual_generator_frame k j) hj hj).symm s) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := (pairedC3FrameEquiv (paired_c3_coordinate_dual_generator_frame k i) hi hi).apply_symm_apply s
  change pairedC3NegativeLineCoordinate k i V hi s •
    pairedC3ModuleRestrict (pairedC3NegativeLine k) hi (pairedC3CoordinateDualGenerator k i) = s at h
  rw [paired_c3_dual_generator_transition_subopen k i j V hi hj] at h
  change s = ((pairedC3Proj k).presheaf.map (homOfLE hi).op
    (ProjSpace.coordinateRatioSection ℂ k i j) * pairedC3NegativeLineCoordinate k i V hi s) •
    pairedC3ModuleRestrict (pairedC3NegativeLine k) hj (pairedC3CoordinateDualGenerator k j)
  rw [mul_comm, mul_smul]
  exact h.symm

#print axioms paired_c3_dual_generator_transition_subopen
#print axioms paired_c3_negative_line_coordinate_restrict
#print axioms paired_c3_negative_line_coordinate_transition
end HodgeLean.Foundations.Program.G32Native
