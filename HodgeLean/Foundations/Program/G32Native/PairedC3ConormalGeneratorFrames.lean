import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalFrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalProjectiveChartFrame

/-! # Freeness of the specified projective conormal generators -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] Classical.propDecidable

/-- The canonical discarded-coordinate ideal classes form a free frame
on every subopen of the original retained-coordinate chart.
Source: Hartshorne, Algebraic Geometry, II.8.12, the affine calculation
of the conormal of a linear coordinate subspace. -/
theorem paired_c3_conormal_standard_generator_frame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (V : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i) :
    Function.Bijective (pairedC3FiniteFrameSynthesis
      (fun j : {j : Fin (n + 1) // j ∉ Set.range e} =>
        pairedC3ConormalStandardGenerator e i j.val j.property) V hi) := by
  exact paired_c3_canonical_projective_chart_frame e i V hi

#print axioms paired_c3_conormal_standard_generator_frame
end HodgeLean.Foundations.Program.G32Native
