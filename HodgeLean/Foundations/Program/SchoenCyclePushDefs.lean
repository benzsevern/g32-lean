import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Rational intersection pairing and finite cycle combinations
The pairing is formed from singular cup product and an explicit trace.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The middle-dimensional cup pairing followed by the specified rational trace.
Source: Schoen (1988), p. 18, rational Poincaré duality; Hatcher, §3.3. -/
def s2e_middlePairing (X : TopCat) (k : ℕ)
    (tr : AlgebraicTopology.Singular.Cohomology ℚ X (2 * (2 * k)) →ₗ[ℚ] ℚ) :
    AlgebraicTopology.Singular.Cohomology ℚ X (2 * k) →ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ X (2 * k) →ₗ[ℚ] ℚ :=
  (HodgeLean.Foundations.Singular.cup X (show 2 * k + 2 * k = 2 * (2 * k) by omega)).compr₂ tr

example (X : TopCat) (k : ℕ)
    (tr : AlgebraicTopology.Singular.Cohomology ℚ X (2 * (2 * k)) →ₗ[ℚ] ℚ) :
    s2e_middlePairing X k tr 0 = 0 := map_zero _

/-- A finite rational combination of the actual component orbit.
Source: Schoen (1988), Theorem 2.0 and p. 18, rational algebraic cycles. -/
def s2e_rationalOrbitCycle {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (a : Fin m → ℚ) :
    AlgebraicCycle W.left ℚ :=
  ∑ t : Fin m, (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ).mapRange
    (a t * ·) (mul_zero _)

example {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (a : Fin m → ℚ) :
    s2e_rationalOrbitCycle ι d m a = ∑ t : Fin m,
      (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ).mapRange
        (a t * ·) (mul_zero _) := rfl

end HodgeLean.Foundations.Program
