import HodgeLean.Adapters.AbelianPowerHodge
import HodgeLean.Adapters.DegreeZeroUnconditional

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- The scalar part of the powers assembly is algebraic, including zero copies.
Source: Fulton, Intersection Theory, §19.1, the cycle class in degree zero. -/
theorem power_hodge_degree_zero : Hdg^0(Y; ℚ) ≤ algebraicCycleClassSpan Y 0 := by
  rw [algebraicCycleClassSpan_zero_eq_top_unconditional Y]
  exact le_top

/-- The power cohomology transport makes all degrees above the dimension algebraic
by vanishing; no invariant generation is needed for these degrees.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., Lemma 1.3.1. -/
theorem power_hodge_above_dimension (power : AbelianPowerData A Y r)
    (p : ℕ) (hp : r * dim A.left < p) :
    Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  rw [spec_g2_hodgeClasses_eq_bot_of_lt power p hp]
  exact bot_le

#print axioms power_hodge_degree_zero
#print axioms power_hodge_above_dimension
end HodgeLean.Foundations.Abdulali
