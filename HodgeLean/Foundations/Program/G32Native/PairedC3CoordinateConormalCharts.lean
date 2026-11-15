import HodgeLean.Foundations.Program.G32Native.PairedC3SplitCoordinateFrames
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusion
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineLinearConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3LinearConormalTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleIso
import HodgeLean.Foundations.Program.G32Native.PairedC3DualGeneratorTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalGeneratorFrames
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalFrameAssembly

/-! # Natural chart comparisons for the standard linear conormal -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- On every standard parameter chart, compare the discarded-coordinate
ideal classes with the dual twisting frames. The comparisons are natural
on subopens and agree on intersections, including their inverse-unit
coefficient transformations.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.7.1. -/
theorem paired_c3_initial_coordinate_chart_comparison_aux
    (k r : ℕ) (hr : 1 < r) :
    Nonempty (PairedC3LocalModuleComparison
      (s2c_conormal (pairedC3InitialCoordinateInclusion k r (by omega)))
      (pairedC3SplitBundle k 0 (r - 1)) (ProjSpace.twistingCover ℂ k)) := by
  classical
  have hpoly : ∀ (m : ℕ) (e : Fin (k + 1) ↪ Fin m),
      Nonempty (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e) ≅
        pairedC3SplitBundle k 0 (m - (k + 1))) := by
    intro m e
    cases m with
    | zero => exact Fin.elim0 (e 0)
    | succ n =>
      have E := pairedC3PolynomialConormalGeneratorIso e
        (paired_c3_conormal_standard_generator_frame e)
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_add_right] using Nonempty.intro E
  let e := pairedC3InitialCoordinateEmbedding k r (by omega)
  let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let a := s2_polynomialProjectiveSpaceIso ℂ (Fin (k + r))
  obtain ⟨E⟩ := hpoly (k + r) e
  have hcount : k + r - (k + 1) = r - 1 := by omega
  let C : s2c_conormal (pairedC3InitialCoordinateInclusion k r (by omega)) ≅
      pairedC3SplitBundle k 0 (r - 1) :=
    s2e_ambientIsoConormalIso p a.hom ≪≫ E ≪≫
      eqToIso (congrArg (pairedC3SplitBundle k 0) hcount)
  exact ⟨pairedC3ComparisonOfIso C (ProjSpace.twistingCover ℂ k)⟩

end HodgeLean.Foundations.Program.G32Native
