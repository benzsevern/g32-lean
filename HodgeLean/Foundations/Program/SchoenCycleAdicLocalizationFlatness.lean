import HodgeLean.Foundations.Program.SchoenCycleAdicMapFlatness
import HodgeLean.Foundations.Program.SchoenCycleCanonicalLocalizationAdic
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMapComp

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Bijectivity of the canonical retained adic map forces flatness of the actual prime localization over the source ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_flat_prime_localization_of_adic_bijective
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing A] [IsNoetherianRing S]
    (I : Ideal A) (Q : Ideal S) [Q.IsMaximal]
    (h : ∀ n a, a ∈ I ^ n → algebraMap A S a ∈ Q ^ n)
    (hbij : Function.Bijective (s2e_adic_algebra_map I Q (Algebra.ofId A S) h)) :
    Module.Flat A (Localization.AtPrime Q) := by
  let B := Localization.AtPrime Q
  let J := IsLocalRing.maximalIdeal B
  let f := IsScalarTower.toAlgHom A S B
  have hg (n : ℕ) (s : S) (hs : s ∈ Q ^ n) : f s ∈ J ^ n := by
    change algebraMap S B s ∈ IsLocalRing.maximalIdeal B ^ n
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q B, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hs
  let E := (s2e_canonical_localization_adic_equiv Q B).restrictScalars A
  have hE : E.toAlgHom = s2e_adic_algebra_map Q J f hg := by
    rfl
  have hc : Function.Bijective (s2e_adic_algebra_map I J (Algebra.ofId A B)
      (fun n a ha => hg n (algebraMap A S a) (h n a ha))) := by
    have hh : Function.Bijective
        (E.toAlgHom.comp (s2e_adic_algebra_map I Q (Algebra.ofId A S) h)) :=
      E.bijective.comp hbij
    rw [hE] at hh
    rw [s2e_adic_algebra_map_comp] at hh
    exact hh
  have hflat := s2e_actual_map_flat_of_adic_bijective A A B I (Algebra.ofId A B) _ hc
  convert hflat using 1
  ext a b
  exact Algebra.smul_def a b

#print axioms s2e_flat_prime_localization_of_adic_bijective
end HodgeLean.Foundations.Program
