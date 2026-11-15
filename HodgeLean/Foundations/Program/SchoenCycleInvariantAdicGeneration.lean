import HodgeLean.Foundations.Program.SchoenCyclePolynomialAdicLocal
import HodgeLean.Foundations.Program.SchoenCycleSymmetricAdicJets

/-! # Local generation in a polynomial adic invariant ring -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Elementary coefficient lifts generate a local ring identified with the
permutation invariants of the polynomial adic ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_adic_maximalIdeal_generators
    (n : ℕ) {S : Type*} [CommRing S] [IsLocalRing S]
    (f : S →+* AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    [IsLocalHom f] (hf : Function.Injective f)
    (hfix : ∀ σ : Equiv.Perm (Fin n), ∀ s, s2e_polynomial_adic_rename σ (f s) = f s)
    (hdesc : ∀ z, (∀ σ : Equiv.Perm (Fin n), s2e_polynomial_adic_rename σ z = z) →
      ∃ s, f s = z)
    (c : Fin n → S)
    (hc : ∀ j, f (c j) = algebraMap (MvPolynomial (Fin n) ℂ)
      (AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
        (esymm (Fin n) ℂ (j.val + 1))) :
    IsLocalRing.maximalIdeal S = Ideal.span (Set.range c) := by
  apply le_antisymm
  · intro s hs
    have hfs := (IsLocalRing.map_maximalIdeal_le f) (Ideal.mem_map_of_mem f hs)
    have h0 := (s2e_polynomial_adic_mem_maximalIdeal_iff_eval (Fin n) (f s)).mp hfs
    obtain ⟨b, hb, he⟩ := s2e_invariant_adic_elementary_invariant_coefficients n (f s)
      (fun σ => hfix σ s) h0
    choose d hd using fun j => hdesc (b j) (fun σ => hb σ j)
    have heq : ∑ j, d j * c j = s := by
      apply hf
      simpa only [map_sum, map_mul, hd, hc] using he
    rw [← heq]
    apply Ideal.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← IsLocalRing.maximalIdeal_comap f]
    change f (c j) ∈ IsLocalRing.maximalIdeal _
    rw [hc, s2e_polynomial_adic_maximalIdeal]
    apply Ideal.mem_map_of_mem
    rw [s2e_idealOfVars_eq_ker_constantCoeff]
    change constantCoeff (esymm (Fin n) ℂ (j.val + 1)) = 0
    exact s2e_constantCoeff_esymm_succ ℂ (Fin n) j.val

#print axioms s2e_invariant_adic_maximalIdeal_generators
end HodgeLean.Foundations.Program
