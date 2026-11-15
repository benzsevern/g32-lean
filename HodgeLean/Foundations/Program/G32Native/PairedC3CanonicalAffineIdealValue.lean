import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartObjects

noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The transported ideal generator has exactly its original normal-ratio kernel value. -/
theorem paired_c3_canonical_affine_ideal_generator_value {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    s2e_affine_ideal_sections_equiv (pairedC3ChartRing n (e i)) (pairedC3ChartRing k i)
      (pairedC3ChartProjection e i) (pairedC3CanonicalAffineIdealGenerator e i j) =
      ⟨ProjSpace.ratio ℂ n (e i) j.val,
        paired_c3_coordinate_chart_map_discarded_ratio e i j.val j.property⟩ := by
  apply Subtype.ext
  have h := paired_c3_affine_chart_ideal_section_value
    (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
    (pairedC3ChartRing n (e i)) (pairedC3ChartRing k i) (pairedC3ChartProjection e i)
    (pairedC3ChartInclusion n (e i)) (pairedC3ChartInclusion k i)
    (paired_c3_chart_diagram_commutes e i)
    (ProjSpace.standardOpen ℂ n (e i)) (paired_c3_chart_inclusion_preimage n (e i))
    (pairedC3ProjectiveIdealGenerator e i j.val j.property)
  conv_rhs at h => simp only [pairedC3ProjectiveIdealGenerator, LinearEquiv.apply_symm_apply]
  exact h.trans (paired_c3_projective_chart_section_value n (e i) (ProjSpace.ratio ℂ n (e i) j.val))

#print axioms paired_c3_canonical_affine_ideal_generator_value
end HodgeLean.Foundations.Program.G32Native
