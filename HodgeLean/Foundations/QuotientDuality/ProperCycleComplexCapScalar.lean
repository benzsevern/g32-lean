import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductOrientation

/-! # The actual scalar of the original complex product normal cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluation by the original normalized standard coclass gives the actual coefficient of every intrinsic complex local homology class.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, complex local homology lines and their normalized duals.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_local_normalized_expansion (r : ℕ)
    (w : orientationGroup (TopCat.of (Fin r → ℂ)) (2 * r) 0) :
    relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ r) (2 * r)
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ r)
          (standardComplexLocalClass_ne_zero_for_chart r)) w • standardComplexLocalClass ℚ r = w := by
  let z := standardComplexLocalClass ℚ r
  let F := relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ r) (2 * r)
    (normalizedRelativeCoclass z (standardComplexLocalClass_ne_zero_for_chart r))
  have hw : w ∈ Submodule.span ℚ ({standardComplexLocalClass ℚ r} : Set _) := by
    rw [span_standardComplexLocalClass_eq_top_for_chart r]
    trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  change F w • z = w
  change c • z = w at hc
  have hFz : F z = 1 := normalizedRelativeCoclass_pairing_self z
    (standardComplexLocalClass_ne_zero_for_chart r)
  rw [← hc, map_smul, hFz, smul_eq_mul, mul_one]

/-- The actual coefficient of the original projected normal cap on the specified standard complex product orientation.
Source: Hatcher, Algebraic Topology, section 3.3, local complex cap orientations.
HC no distance; AV milestone no distance. -/
def properCycle_standard_complex_cap_scalar (r d : ℕ) : ℚ :=
  relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ r) (2 * r)
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ r)
      (standardComplexLocalClass_ne_zero_for_chart r))
    (properCycle_standard_complex_local_cap r d (properCycle_complex_product_standard_orientation r d))

/-- The original normal cap sends the specified actual complex product orientation to its actual scalar times the original intrinsic standard complex orientation.
Source: Hatcher, Algebraic Topology, section 3.3, the scalar of local complex cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_complex_cap_scalar_formula (r d : ℕ) :
    properCycle_standard_complex_cap_scalar r d • standardComplexLocalClass ℚ r =
      properCycle_standard_complex_local_cap r d (properCycle_complex_product_standard_orientation r d) :=
  properCycle_standard_local_normalized_expansion r _

/-- The actual scalar of the original complex product normal cap is nonzero, as follows from its constructed local duality and the specified original ambient orientation.
Source: Hatcher, Algebraic Topology, section 3.3, nonvanishing of local complex cap orientations.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_complex_cap_scalar_ne_zero (r d : ℕ) :
    properCycle_standard_complex_cap_scalar r d ≠ 0 := by
  intro h
  have hf := properCycle_standard_complex_cap_scalar_formula r d
  rw [h, zero_smul] at hf
  apply properCycle_complex_product_standard_orientation_ne_zero r d
  apply (properCycle_standard_complex_local_cap_bijective r d).1
  rw [map_zero]
  exact hf.symm

end HodgeLean.Foundations.QuotientDuality
