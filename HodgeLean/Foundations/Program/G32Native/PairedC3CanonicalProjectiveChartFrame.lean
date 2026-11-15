import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartFrame

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

/-- The same canonical normal classes frame every original projective chart
subopen, through the original open-immersion section maps. -/
theorem paired_c3_canonical_projective_chart_frame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (V : (pairedC3Proj k).Opens) (hi : V ≤ ProjSpace.standardOpen ℂ k i) :
    Function.Bijective (pairedC3FiniteFrameSynthesis
      (fun j : {j : Fin (n + 1) // j ∉ Set.range e} =>
        pairedC3ConormalStandardGenerator e i j.val j.property) V hi) := by
  have hU : ProjSpace.standardOpen ℂ k i ≤ (pairedC3ChartInclusion k i).opensRange :=
    (Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X ℂ i) (by omega)).ge
  exact paired_c3_open_frame_transfer (pairedC3ChartInclusion k i)
    (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))
    (ProjSpace.standardOpen ℂ k i) hU (paired_c3_projective_chart_preimage k i)
    (fun j : {j : Fin (n + 1) // j ∉ Set.range e} =>
      pairedC3ConormalStandardGenerator e i j.val j.property)
    (paired_c3_canonical_affine_chart_frame e i) V hi

#print axioms paired_c3_canonical_projective_chart_frame
end HodgeLean.Foundations.Program.G32Native
