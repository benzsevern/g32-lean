import HodgeLean.Adapters.CyclePushforward
import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.SchoenCycleDualityHelpers
import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import Other.AlgebraicTopology.Singular.EmptySubspace

/-! # Geometric cycles and proper transfer models

The cycle map uses residue fields. Pairings use actual singular cup products
and evaluation on specified fundamental classes.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The coefficient-one prime at its actual scheme point.
Source: Fulton, Intersection Theory, second edition, section 1.4.
HC no distance; AV milestone no distance. -/
def properPrime {X : Scheme.{0}} (x : X) : AlgebraicCycle X ℚ := by
  classical
  exact Function.locallyFinsuppWithin.single x (1 : ℚ)

example {X : Scheme.{0}} (x : X) : properPrime x x = (1 : ℚ) := by
  classical
  simp [properPrime]

/-- Middle cup pairing with the specified singular fundamental class.
Source: Fulton, Intersection Theory, section 19.2; Hatcher, section 3.3.
HC no distance; AV milestone no distance. -/
def properCyclePairing (X : TopCat.{0}) (k : ℕ)
    (c : Homology ℚ X (2 * (2 * k))) :=
  s2e_middlePairing X k (orientationIntegral X (2 * (2 * k)) c)

example (X : TopCat.{0}) (k : ℕ) (c : Homology ℚ X (2 * (2 * k))) :
    properCyclePairing X k c (0 : Cohomology ℚ X (2 * k)) = 0 := map_zero _

/-- Supported pushforward in the homeomorphism model is inverse pullback.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
def supportHomeomorphTransfer {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (Z : Set X) (n : ℕ) : CohomologyWithSupport ℚ X Z n →ₗ[ℚ]
      CohomologyWithSupport ℚ Y (e.symm ⁻¹' Z) n :=
  cohomologyWithSupportMap ℚ n (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) Z

example {X Y : TopCat.{0}} (e : X ≃ₜ Y) (Z : Set X) (n : ℕ) :
    supportHomeomorphTransfer e Z n 0 = 0 := map_zero _

end HodgeLean.Foundations.QuotientDuality
