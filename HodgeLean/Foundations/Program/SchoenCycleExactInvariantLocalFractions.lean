import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An exactly invariant local element at a fixed prime has an actual invariant numerator and invariant denominator nonvanishing at that prime.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_exact_invariant_local_fraction
    (C B G : Type*) [CommRing C] [IsDomain C] [CommRing B] [Algebra C B]
    [Group G] [Fintype G] [MulSemiringAction G C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (hP : ∀ (g : G) (c : C), g • c ∈ P ↔ c ∈ P)
    (β : G → (B →+* B))
    (hβ : ∀ (g : G) (c : C), β g (algebraMap C B c) = algebraMap C B (g • c))
    (r : B) (hr : ∀ g, β g r = r) :
    ∃ a d : C, (∀ g : G, g • a = a) ∧ (∀ g : G, g • d = d) ∧
      d ∉ P ∧ algebraMap C B a = r * algebraMap C B d := by
  classical
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
  let d : C := ∏ g : G, g • s.val
  have hd : ∀ g : G, g • d = d := Finset.smul_prod_perm s.val
  have hdP : d ∉ P := by
    change d ∈ P.primeCompl
    apply Submonoid.prod_mem
    intro g _
    change g • s.val ∉ P
    exact fun h => s.property ((hP g s.val).mp h)
  have hsd : s.val ∣ d := by
    have hh := Finset.dvd_prod_of_mem (fun g : G => g • s.val) (Finset.mem_univ (1 : G))
    simpa only [one_smul] using hh
  obtain ⟨q, hq⟩ := hsd
  have hrs : r * algebraMap C B s.val = algebraMap C B a := by
    rw [← hs]
    exact IsLocalization.mk'_spec B a s
  have hnum : algebraMap C B (a * q) = r * algebraMap C B d := by
    rw [map_mul, ← hrs, hq, map_mul, mul_assoc]
  have hinj : Function.Injective (algebraMap C B) := IsLocalization.injective B (M := P.primeCompl) (by
    intro c hc
    change c ∉ P at hc
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    exact hc (hz ▸ P.zero_mem))
  refine ⟨a * q, d, ?_, hd, hdP, hnum⟩
  intro g
  apply hinj
  rw [← hβ, hnum, map_mul, hr, hβ, hd]

#print axioms s2e_exact_invariant_local_fraction
end HodgeLean.Foundations.Program
