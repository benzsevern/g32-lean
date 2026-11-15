import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusion
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineLinearConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3LinearConormalTransitions
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalZero
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateConormalCharts

/-! # The conormal of the standard projective coordinate inclusion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The zero-codimension standard inclusion has its actual empty frame. -/
theorem paired_c3_initial_coordinate_conormal_one (k : ℕ) :
    Nonempty (s2c_conormal (pairedC3InitialCoordinateInclusion k 1 (by omega)) ≅
      pairedC3SplitBundle k 0 0) := by
  rw [paired_c3_initial_coordinate_inclusion_one]
  exact ⟨pairedC3IsomorphismConormalFrame
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom⟩

/-- The independent discarded coordinates give the negative linear
conormal on the original polynomial projective parameter scheme.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.7.1. -/
theorem paired_c3_initial_coordinate_conormal_aux (k r : ℕ) (hr : 0 < r) :
    Nonempty (s2c_conormal (pairedC3InitialCoordinateInclusion k r hr) ≅
      pairedC3SplitBundle k 0 (r - 1)) := by
  by_cases h : r = 1
  · subst r
    exact paired_c3_initial_coordinate_conormal_one k
  have hr' : 1 < r := by omega
  obtain ⟨D⟩ := paired_c3_initial_coordinate_chart_comparison_aux k r hr'
  exact ⟨pairedC3LocalModuleIso D (ProjSpace.iSup_twistingCover ℂ k)⟩

end HodgeLean.Foundations.Program.G32Native
