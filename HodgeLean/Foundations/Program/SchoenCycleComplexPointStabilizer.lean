import HodgeLean.Foundations.Program.SchoenCycleAffinePointStabilizer
import Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fixing an actual complex point is equivalent to fixing its affine prime by the actual section comap.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_point_fixed_iff_prime_comap
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ X) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hUP : U ≤ f.left ⁻¹ᵁ U) (x : ComplexPoint X) (hx : x.underlying ∈ U) :
    Point.map f x = x ↔
      (hU.primeIdealOf ⟨x.underlying, hx⟩).asIdeal.comap (f.left.appLE U U hUP).hom =
        (hU.primeIdealOf ⟨x.underlying, hx⟩).asIdeal := by
  rw [← s2e_affine_point_fixed_iff_prime_comap X.left f.left U hU hUP x.underlying hx]
  constructor
  · intro h
    exact congrArg Point.underlying h
  · intro h
    apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
    exact h

#print axioms s2e_complex_point_fixed_iff_prime_comap
end HodgeLean.Foundations.Program
