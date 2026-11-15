import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartCap

/-! # Independent positive-dimensional partial-chart cap checks

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartCapChecks

private abbrev P := (Fin 1 → ℂ) × (Fin 1 → ℂ)
private def e : OpenPartialHomeomorph P P := (Homeomorph.refl P).toOpenPartialHomeomorph
private def E : (Set.univ : Set P) ≃ₜ P := Homeomorph.Set.univ P
private def α := relativeCohomologyMap ℚ 2
  (TopPair.isoOfSubset (X := TopCat.of (Set.univ : Set P)) (Y := TopCat.of P)
    (A := {w | (e w.val).2 ≠ 0}) (B := {z | z.2 ≠ 0}) E (fun _ => Iff.rfl)).hom
  (relativeCohomologyMap ℚ 2
    (properCycle_product_support_projection (Fin 1 → ℂ) (TopCat.of (Fin 1 → ℂ)) {0})
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ 1)
      (standardComplexLocalClass_ne_zero_for_chart 1)))
private def K := properCycle_partial_chart_cap (M := TopCat.of P) 1 1 e
  (0, 0) (by trivial) rfl Set.univ (fun _ h => h) isOpen_univ (Set.mem_univ _)
private def c := properCycle_complex_product_standard_orientation 1 1

private lemma K_bijective : Function.Bijective (K α) :=
  properCycle_partial_chart_cap_bijective (M := TopCat.of P) 1 1 e (0, 0) (by trivial) rfl
    Set.univ (fun _ h => h) isOpen_univ (Set.mem_univ _) E (fun _ => rfl)

private lemma c_ne_zero : c ≠ 0 := properCycle_complex_product_standard_orientation_ne_zero 1 1

/-- The constructed chart cap in one complex tangential and one complex normal dimension does not kill the specified original complex orientation.
Source: Hatcher, Algebraic Topology, section 3.3, local cap duality.
HC no distance; AV milestone no distance. -/
theorem chart_cap_nonzero : K α c ≠ 0 := by
  intro h
  exact c_ne_zero (K_bijective.injective (h.trans (map_zero (K α)).symm))

example : K α c ≠ 0 := chart_cap_nonzero

/-- Reversing the actual ambient orientation changes the actual partial-chart cap value.
Source: Hatcher, Algebraic Topology, section 3.3, orientation and cap bilinearity.
HC no distance; AV milestone no distance. -/
theorem partial_chart_cap_normalization_orientation_falsification : K α (-c) ≠ K α c := by
  intro h
  have hc : -c = c := K_bijective.injective h
  have hz : (2 : ℚ) • c = 0 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, add_smul, one_smul]
    exact neg_eq_iff_add_eq_zero.mp hc
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) c_ne_zero) hz

example : K α (-c) ≠ K α c := partial_chart_cap_normalization_orientation_falsification

/-- Doubling the supplied normal coclass changes the cap on the original ambient orientation.
Source: Fulton, Intersection Theory, section 19.1, multiplicity normalization.
HC no distance; AV milestone no distance. -/
theorem partial_chart_cap_normalization_multiplicity_falsification : K ((2 : ℚ) • α) c ≠ K α c := by
  intro h
  have hh : (2 : ℚ) • K α c = K α c := by simpa only [map_smul, LinearMap.smul_apply] using h
  have hz : ((2 : ℚ) - 1) • K α c = 0 := by rw [sub_smul, one_smul, hh, sub_self]
  exact (smul_ne_zero (by norm_num : (2 : ℚ) - 1 ≠ 0) chart_cap_nonzero) hz

example : K ((2 : ℚ) • α) c ≠ K α c := partial_chart_cap_normalization_multiplicity_falsification

private def L : P ≃L[ℂ] (Fin (1 + 1) → ℂ) := ContinuousLinearEquiv.ofFinrankEq
  (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
private def β := relativeCohomologyMap ℚ 2
  (properCycle_product_support_projection (Fin 1 → ℂ) (TopCat.of (Fin 1 → ℂ)) {0})
  (normalizedRelativeCoclass (standardComplexLocalClass ℚ 1)
    (standardComplexLocalClass_ne_zero_for_chart 1))
private def compressed := localClassOfChart (1 + 1) L.toHomeomorph.toOpenPartialHomeomorph
  (0, 0) (by trivial)

/-- The actual standard diagram, with its original compressed chart class, retains the literal multiplicity three and the specified common scalar.
Source: Hatcher, Algebraic Topology, section 3.3; Fulton, Intersection Theory, section 19.1.
HC no distance; AV milestone no distance. -/
theorem partial_chart_cap_normalization_scalar_example :
    properCycle_complex_product_local_cap 1 1 ((3 : ℚ) • β) compressed =
      ((3 : ℚ) * properCycle_standard_complex_cap_scalar 1 1) • standardComplexLocalClass ℚ 1 :=
  properCycle_complex_chart_cap_multiplicity 1 1 3

example : properCycle_complex_product_local_cap 1 1 ((3 : ℚ) • β) compressed =
    ((3 : ℚ) * properCycle_standard_complex_cap_scalar 1 1) • standardComplexLocalClass ℚ 1 :=
  partial_chart_cap_normalization_scalar_example

/-- Negating the stated scalar fails on the actual compressed standard chart diagram in positive tangential and normal dimensions.
Source: Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
theorem partial_chart_cap_normalization_scalar_falsification :
    properCycle_complex_product_local_cap 1 1 ((3 : ℚ) • β) compressed ≠
      (-((3 : ℚ) * properCycle_standard_complex_cap_scalar 1 1)) • standardComplexLocalClass ℚ 1 := by
  rw [partial_chart_cap_normalization_scalar_example]
  intro h
  have hs := smul_left_injective ℚ (standardComplexLocalClass_ne_zero_for_chart 1) h
  have hn := properCycle_standard_complex_cap_scalar_ne_zero 1 1
  apply hn
  linarith

example : properCycle_complex_product_local_cap 1 1 ((3 : ℚ) • β) compressed ≠
    (-((3 : ℚ) * properCycle_standard_complex_cap_scalar 1 1)) • standardComplexLocalClass ℚ 1 :=
  partial_chart_cap_normalization_scalar_falsification

end HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartCapChecks
