import HodgeLean.Foundations.Program.SchoenTowerL1aPolynomialAction
import HodgeLean.Foundations.Program.SchoenTowerL1aRationalStabilizers

/-! # Stabilizers of actual polynomial parameter values

Implication from separated support values to preservation of the rational
point stabilizer under the polynomial parameter map.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The polynomial evaluation kernel has precisely the stabilizer of its
actual parameter tuple, in the inverse permutation convention.
Source: Hartshorne, Algebraic Geometry, II.2, rational points of affine space. -/
theorem s2v_l1a_polynomial_kernel_stabilizer
    {K ι : Type*} [CommRing K] (z : ι → K) (g : Equiv.Perm ι) :
    letI := s2v_l1a_polynomialPermutationAction K ι
    g • RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom ↔
        ∀ i, z (g⁻¹ i) = z i := by
  letI := s2v_l1a_polynomialPermutationAction K ι
  letI := s2v_l1a_polynomialPermutationAction_scalars K ι
  rw [s2v_l1a_rational_kernel_stabilizer]
  constructor
  · intro h i
    have H := congrArg (fun F : MvPolynomial ι K →ₐ[K] K => F (MvPolynomial.X i)) h
    change MvPolynomial.aeval (R := K) z (MvPolynomial.rename (g⁻¹ : Equiv.Perm ι) (MvPolynomial.X i)) = MvPolynomial.aeval (R := K) z (MvPolynomial.X i) at H
    simpa only [MvPolynomial.rename_X, MvPolynomial.aeval_X] using H
  · intro h
    apply MvPolynomial.algHom_ext
    intro i
    change MvPolynomial.aeval (R := K) z (MvPolynomial.rename (g⁻¹ : Equiv.Perm ι) (MvPolynomial.X i)) =
      MvPolynomial.aeval (R := K) z (MvPolynomial.X i)
    rw [MvPolynomial.rename_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact h i

/-- A parameter separating the support of a tuple preserves its actual
permutation stabilizer, including tuples with repetitions.
Source: Schoen (1988), Lemma 2.2, printed p. 13, separating curve parameters. -/
theorem s2v_l1a_separating_tuple_stabilizer
    {ι T K : Type*} (p : ι → T) (f : T → K)
    (hsep : ∀ i j, p i ≠ p j → f (p i) ≠ f (p j)) (g : Equiv.Perm ι) :
    (∀ i, f (p (g⁻¹ i)) = f (p i)) ↔ ∀ i, p (g⁻¹ i) = p i := by
  constructor
  · intro h i
    by_contra hne
    exact hsep (g⁻¹ i) i hne (h i)
  · intro h i
    exact congrArg f (h i)

end HodgeLean.Foundations.Program
