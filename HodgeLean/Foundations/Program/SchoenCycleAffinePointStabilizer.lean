import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Stabilizing a point in an invariant affine neighbourhood is equivalent to stabilizing its actual prime ideal by section comap.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_point_fixed_iff_prime_comap
    (X : Scheme) (f : X ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hUP : U ≤ f ⁻¹ᵁ U) (p : X) (hp : p ∈ U) :
    f p = p ↔
      (hU.primeIdealOf ⟨p, hp⟩).asIdeal.comap (f.appLE U U hUP).hom =
        (hU.primeIdealOf ⟨p, hp⟩).asIdeal := by
  have hc := IsAffineOpen.comap_primeIdealOf_appLE U hU U hU hUP hp
  constructor
  · intro hfix
    simpa only [PrimeSpectrum.comap_asIdeal, hfix] using congrArg PrimeSpectrum.asIdeal hc
  · intro hI
    have he : hU.primeIdealOf ⟨f p, hUP hp⟩ = hU.primeIdealOf ⟨p, hp⟩ := by
      apply PrimeSpectrum.ext
      exact (congrArg PrimeSpectrum.asIdeal hc).symm.trans hI
    have hx := congrArg hU.fromSpec he
    simpa only [hU.fromSpec_primeIdealOf] using hx

#print axioms s2e_affine_point_fixed_iff_prime_comap
end HodgeLean.Foundations.Program
