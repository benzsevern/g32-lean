import HodgeLean.Foundations.QuotientDuality.ProperCycleSplitChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicZeroExtension
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSmoothExtension
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicPositiveExtension
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicLocalDegree

/-! # Intrinsic complex top classes across smaller algebraic boundaries

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The complex top class on the intrinsic regular locus extends uniquely across its smaller algebraic singular boundary. The resulting class generates the actual ordinary top homology of the projective integral space.
Source: Bredon, Sheaf Theory, second edition, V.9, complex orientation and the localization sequence; Fulton, Intersection Theory, section 19.1.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_extension_aux
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    ∃! c : Homology ℚ (a3b4_an V.hom) (2 * d),
      (∀ (e : OpenPartialHomeomorph (ComplexPoint V) (Fin d → ℂ)),
        (∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i)) →
        ∀ (x : ComplexPoint V) (hx : x ∈ e.source),
          localOrientation (a3b4_an V.hom) (2 * d) c x = localClassOfChart d e x hx) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ
        (Homology ℚ (a3b4_an V.hom) (2 * d)) c) := by
  by_cases hd : d = 0
  · subst d
    simpa only [Nat.mul_zero] using properCycle_zero_dimensional_intrinsic_extension V hdim
  · by_cases hs : Smooth V.hom
    · letI := hs
      have hdim' : TopologicalSpace.dim V.left = d := by
        unfold TopologicalSpace.dim
        rw [hdim]
        rfl
      letI : SmoothOfRelativeDimension d V.hom := by
        rw [← hdim']
        infer_instance
      exact properCycle_smooth_intrinsic_extension V d
    · exact properCycle_positive_intrinsic_extension V d (by omega) hdim

example := ProperCycleSplitChecks.intrinsic_extension_point_example

end HodgeLean.Foundations.QuotientDuality
