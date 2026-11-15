import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual complex point supplied by an affine augmentation has exactly its kernel as underlying prime ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_spec_point_prime
    (S : Type) [CommRing S] [Algebra ℂ S] (ε : S →ₐ[ℂ] ℂ) :
    ((ComplexPoint.affineSpecEquiv S).symm ε).underlying.asIdeal = RingHom.ker ε.toRingHom := by
  change (IsLocalRing.maximalIdeal ℂ).comap ε.toRingHom = RingHom.ker ε.toRingHom
  rw [IsLocalRing.maximalIdeal_eq_bot (R := ℂ)]
  rfl

#print axioms s2e_affine_spec_point_prime
end HodgeLean.Foundations.Program
