import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticDerivation
import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps

/-! # Finite and adic coordinates for native analytic germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical polynomial map is bijective on every native analytic
maximal-ideal power quotient.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_nativeAnalytic_finite_coordinates_bijective (d N : ℕ) :
    Function.Bijective (s2e_adic_quotient_ring_map (MvPolynomial.idealOfVars (Fin d) ℂ)
      (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
      (s2e_nativeAnalytic_polynomial d) (s2e_nativeAnalytic_map_variableIdeal d).le N) := by
  constructor
  · intro a b hab
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    apply (s2e_nativeAnalytic_polynomial_order_iff d N (p - q)).mp
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hab
  · intro b
    obtain ⟨p, hp⟩ := s2e_nativeAnalytic_polynomial_quotient_surjective d N b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩

#print axioms s2e_nativeAnalytic_finite_coordinates_bijective
/-- Polynomial coordinates induce a ring equivalence on the adic rings
of the polynomial variable ideal and native analytic maximal ideal.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_nativeAnalytic_adic_coordinates (d : ℕ) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin d) ℂ) (MvPolynomial (Fin d) ℂ) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
        (s2e_nativeAnalyticGermRing d) :=
  RingEquiv.ofBijective
    (s2e_adic_ring_map (MvPolynomial.idealOfVars (Fin d) ℂ)
      (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
      (s2e_nativeAnalytic_polynomial d) (s2e_nativeAnalytic_map_variableIdeal d).le)
    (s2e_adic_ring_map_bijective _ _ _ _ (s2e_nativeAnalytic_finite_coordinates_bijective d))

#print axioms s2e_nativeAnalytic_adic_coordinates
/-- Native analytic adic coordinates extend evaluation of the original
polynomials in analytic coordinate germs.
Source: Mathlib, AdicCompletion.of and ideal-adic functoriality. -/
theorem s2e_nativeAnalytic_adic_coordinates_of (d : ℕ) (p : MvPolynomial (Fin d) ℂ) :
    s2e_nativeAnalytic_adic_coordinates d
      (AdicCompletion.of (MvPolynomial.idealOfVars (Fin d) ℂ) (MvPolynomial (Fin d) ℂ) p) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
        (s2e_nativeAnalyticGermRing d) (s2e_nativeAnalytic_polynomial d p) := by
  exact s2e_adic_ring_map_of _ _ _ _ p

#print axioms s2e_nativeAnalytic_adic_coordinates_of
end HodgeLean.Foundations.Program
