import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCapScalar
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapUnit
import HodgeLean.Foundations.QuotientDuality.RetainedCycleMiddleCapPerfect
import HodgeLean.Foundations.QuotientDuality.RetainedCycleChecks
import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSplitChecks

/-! # Mutation inventory for the consumer split

These reuse independent evaluations of actual supported classes and the specified shifted comparison.
The point cap tests evaluate the actual unit map and reject zero maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality.ConsumerChecks

/-- Independent model for the intrinsic fundamental class sign mutation.
Source: RetainedCycleGlobalChecks.check_intrinsic_global_supported_integration.
HC no distance; AV milestone no distance. -/
theorem intrinsic_fundamental_class_sign : type_of% RetainedCycleGlobalChecks.check_intrinsic_global_supported_integration :=
  RetainedCycleGlobalChecks.check_intrinsic_global_supported_integration
example := intrinsic_fundamental_class_sign

/-- Independent model for the intrinsic supported class sign mutation.
Source: RetainedCycleChecks.check_intrinsic_supported_integration_equation.
HC no distance; AV milestone no distance. -/
theorem intrinsic_supported_class_sign : type_of% RetainedCycleChecks.check_intrinsic_supported_integration_equation :=
  RetainedCycleChecks.check_intrinsic_supported_integration_equation
example := intrinsic_supported_class_sign

/-- The intrinsic nonzero axis orientation in a singular ambient space rejects sign reversal.
Source: RetainedCycleChecks.check_intrinsic_prime_supported_duality.
HC no distance; AV milestone no distance. -/
theorem intrinsic_supported_class_axis_sign :
    type_of% RetainedCycleChecks.check_intrinsic_prime_supported_duality :=
  RetainedCycleChecks.check_intrinsic_prime_supported_duality
example := intrinsic_supported_class_axis_sign

/-- Independent model for the supported weighted realization zero mutation.
Source: RetainedCycleChecks.check_intrinsic_supported_additivity.
HC no distance; AV milestone no distance. -/
theorem supported_weighted_realization_zero : type_of% RetainedCycleChecks.check_intrinsic_supported_additivity :=
  RetainedCycleChecks.check_intrinsic_supported_additivity
example := supported_weighted_realization_zero

/-- Independent model for the supported transfer zero mutation.
Source: RetainedCycleGlobalChecks.check_even_middle_retained_transport.
HC no distance; AV milestone no distance. -/
theorem supported_transfer_zero : type_of% RetainedCycleGlobalChecks.check_even_middle_retained_transport :=
  RetainedCycleGlobalChecks.check_even_middle_retained_transport
example := supported_transfer_zero

/-- Independent model for the intrinsic degree scale mutation.
Source: RetainedCycleChecks.check_retained_orbit_coefficients.
HC no distance; AV milestone no distance. -/
theorem intrinsic_degree_scale : type_of% RetainedCycleChecks.check_retained_orbit_coefficients :=
  RetainedCycleChecks.check_retained_orbit_coefficients
example := intrinsic_degree_scale

/-- Independent model for the supported prime transfer sign mutation.
Source: RetainedCycleChecks.check_retained_supported_pushforward_equality.
HC no distance; AV milestone no distance. -/
theorem supported_prime_transfer_sign : type_of% RetainedCycleChecks.check_retained_supported_pushforward_equality :=
  RetainedCycleChecks.check_retained_supported_pushforward_equality
example := supported_prime_transfer_sign

/-- Independent model for the derived supported normalization sign mutation.
Source: ProperCycleDerivedSplitChecks.middle_support_identification_sign_falsification.
HC no distance; AV milestone no distance. -/
theorem derived_supported_normalization_sign : type_of% ProperCycleDerivedSplitChecks.middle_support_identification_sign_falsification :=
  ProperCycleDerivedSplitChecks.middle_support_identification_sign_falsification
example := derived_supported_normalization_sign

/-- The actual complex cap scalar retains a nonzero local class and rejects a factor two.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_standard_complex_cap_scalar_formula; properCycle_standard_complex_cap_scalar_ne_zero.
HC no distance; AV milestone no distance. -/
theorem derived_cap_scalar_scale :
    properCycle_standard_complex_cap_scalar 1 1 • standardComplexLocalClass ℚ 1 =
      properCycle_standard_complex_local_cap 1 1 (properCycle_complex_product_standard_orientation 1 1) ∧
    properCycle_standard_complex_cap_scalar 1 1 • standardComplexLocalClass ℚ 1 ≠
      (2 : ℚ) • (properCycle_standard_complex_cap_scalar 1 1 • standardComplexLocalClass ℚ 1) := by
  have hn : properCycle_standard_complex_cap_scalar 1 1 • standardComplexLocalClass ℚ 1 ≠ 0 :=
    smul_ne_zero (properCycle_standard_complex_cap_scalar_ne_zero 1 1)
      (standardComplexLocalClass_ne_zero_for_chart 1)
  refine ⟨properCycle_standard_complex_cap_scalar_formula 1 1, ?_⟩
  intro h
  have he := (smul_left_injective ℚ hn) ((one_smul ℚ _).trans h)
  norm_num at he
example := derived_cap_scalar_scale

private abbrev capPoint := TopCat.of PUnit
private def capClass : Homology ℚ capPoint 0 :=
  (asIso (capPoint.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom (1 : ℚ)
private theorem capClass_ne : capClass ≠ 0 := by
  have he : (capPoint.singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom capClass = 1 :=
    LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (Iso.inv_hom_id
        (asIso (capPoint.singularHomology₀ε (ModuleCat.of ℚ ℚ))))) 1
  intro h
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Actual point cap on the unit is nonzero; the zero-map mutation fails injectivity.
Source: Hatcher, Algebraic Topology, section 3.3; retained_cap_with_orientation_unit.
HC no distance; AV milestone no distance. -/
theorem middle_cap_injective_zero :
    retainedMiddleCapWithOrientation capPoint 0 capClass
      (HodgeLean.Foundations.Singular.unit capPoint) = capClass ∧
    retainedMiddleCapWithOrientation capPoint 0 capClass
      (HodgeLean.Foundations.Singular.unit capPoint) ≠ 0 ∧
    ¬ Function.Injective (0 : Cohomology ℚ capPoint 0 →ₗ[ℚ] Homology ℚ capPoint 0) := by
  have hu : retainedMiddleCapWithOrientation capPoint 0 capClass
      (HodgeLean.Foundations.Singular.unit capPoint) = capClass :=
    retained_cap_with_orientation_unit capPoint 0 capClass
  refine ⟨hu, by rw [hu]; exact capClass_ne, ?_⟩
  intro hi
  exact HodgeLean.Foundations.Singular.unit_ne_zero capPoint
    (hi (show (0 : Cohomology ℚ capPoint 0 →ₗ[ℚ] Homology ℚ capPoint 0)
      (HodgeLean.Foundations.Singular.unit capPoint) =
      (0 : Cohomology ℚ capPoint 0 →ₗ[ℚ] Homology ℚ capPoint 0) 0 from rfl))
example := middle_cap_injective_zero

/-- The unit cap reaches a nonzero point class; the zero-map mutation misses it.
Source: Hatcher, Algebraic Topology, section 3.3; retained_cap_with_orientation_unit.
HC no distance; AV milestone no distance. -/
theorem middle_cap_surjective_zero :
    (∃ a, retainedMiddleCapWithOrientation capPoint 0 capClass a = capClass) ∧
    ¬ Function.Surjective (0 : Cohomology ℚ capPoint 0 →ₗ[ℚ] Homology ℚ capPoint 0) := by
  refine ⟨⟨HodgeLean.Foundations.Singular.unit capPoint,
    middle_cap_injective_zero.1⟩, ?_⟩
  intro hs
  obtain ⟨a, ha⟩ := hs capClass
  exact capClass_ne ha.symm
example := middle_cap_surjective_zero

end HodgeLean.Foundations.QuotientDuality.ConsumerChecks
