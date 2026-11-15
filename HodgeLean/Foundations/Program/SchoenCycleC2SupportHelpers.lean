import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Foundations.Program.SchoenCycleC2ExcisionHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The component cycle has exactly one nonzero prime coefficient. -/
theorem s2e_componentCycle_support {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) :
    (s2e_componentCycle ι ℚ).support = {ι.left (genericPoint Q.left)} := by
  classical
  ext x
  simp only [Function.locallyFinsuppWithin.support, Function.mem_support,
    s2e_componentCycle, Function.locallyFinsuppWithin.single_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp only [h, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]

/-- The scheme support of a component cycle is the actual immersion range. -/
theorem s2e_componentCycle_closure {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] :
    closure {ι.left (genericPoint Q.left)} = Set.range ι.left := by
  rw [← Set.image_singleton, ι.left.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ]

/-- The analytic support of a component cycle uses the same scheme range. -/
theorem s2e_componentCycle_analytic_support
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] :
    a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) =
      Point.underlying ⁻¹' Set.range ι.left := by
  simp only [a3b4_cycleSupport, s2e_componentCycle_support, Set.biUnion_singleton,
    s2e_componentCycle_closure]

/-- A neighbourhood of the component contains its entire analytic support. -/
theorem s2e_componentCycle_analytic_support_subset
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) :
    a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ⊆ Point.underlying ⁻¹' (U : Set W.left) := by
  rw [s2e_componentCycle_analytic_support]
  exact Set.preimage_mono hU

/-- Restriction to a scheme neighbourhood of the component is bijective on
its actual rational supported class group. -/
theorem s2e_componentCycle_supported_excision
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) (k : ℕ) :
    Function.Bijective (AlgebraicTopology.Singular.relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap (Point.underlying ⁻¹' (U : Set W.left))
        (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)))) := by
  have hopen : IsOpen (Point.underlying ⁻¹' (U : Set W.left) : Set (ComplexPoint W)) :=
    U.isOpen.preimage (ComplexPoint.continuous_underlying_to_zariski W)
  have hsupport : IsClosed (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)) := by
    rw [s2e_componentCycle_analytic_support]
    exact ι.left.isClosedEmbedding.isClosed_range.preimage
      (ComplexPoint.continuous_underlying_to_zariski W)
  exact s2e_supportedCohomology_excision hopen hsupport
    (s2e_componentCycle_analytic_support_subset ι U hU) (2 * k)

end HodgeLean.Foundations.Program
