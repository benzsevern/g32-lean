import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical adic map of localization at a maximal ideal, retaining its action on every finite quotient coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
def s2e_canonical_localization_adic_equiv
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] [IsLocalRing S] :
    AdicCompletion p R ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal S) S := by
  have hp : ∀ n r, r ∈ p ^ n → algebraMap R S r ∈ IsLocalRing.maximalIdeal S ^ n := by
    intro n r hr
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p S, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  apply AlgEquiv.ofBijective (s2e_adic_algebra_map p (IsLocalRing.maximalIdeal S)
    (Algebra.ofId R S) hp)
  apply s2e_adic_algebra_map_bijective
  intro n
  exact ⟨IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n, fun _ => rfl⟩

end HodgeLean.Foundations.Program
