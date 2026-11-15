import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveStrongSupportCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCapIndependence

/-! # Choice independence of the actual original projective support cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The original projective support cap agrees with the cap from every actual retained collar, with no new geometric hypothesis.
Source: ProperCycleSupportCollar.cap_eq_of_fixed; properCycle_projective_strong_support_collar.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_support_cap_eq_collar
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left)
    (C : ProperCycleSupportCollar (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)))
    (p q : ℕ) (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p + q)) :
    properCycle_projective_support_cap X S p q c =
      C.cap (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c := by
  let B := properCycle_projective_strong_support_collar X S
  have h0 := B.collar.cap_eq_of_fixed (properCycle_projective_support_collar X S)
    B.fixed (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c
  have hC := B.collar.cap_eq_of_fixed C B.fixed
    (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c
  exact h0.trans hC.symm

end HodgeLean.Foundations.QuotientDuality
