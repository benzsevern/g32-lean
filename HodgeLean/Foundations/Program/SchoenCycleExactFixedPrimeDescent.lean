import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationMap
import HodgeLean.Foundations.Program.SchoenCycleExactInvariantLocalFractions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every exactly invariant actual local function descends through the actual localization map from the fixed-function algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_exact_fixed_prime_local_descent
    (k C B G : Type*) [CommRing k] [CommRing C] [IsDomain C] [CommRing B]
    [Algebra k C] [Algebra C B] [Group G] [Fintype G]
    [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (hP : ∀ (g : G) (c : C), g • c ∈ P ↔ c ∈ P)
    (β : G → (B →+* B))
    (hβ : ∀ (g : G) (c : C), β g (algebraMap C B c) = algebraMap C B (g • c))
    (r : B) (hr : ∀ g, β g r = r) :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    ∃ t : Localization.AtPrime Q, s2e_fixed_prime_localization_map k C B G P t = r := by
  classical
  obtain ⟨a, d, ha, hd, hdP, had⟩ := s2e_exact_invariant_local_fraction C B G P hP β hβ r hr
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  let aS : S := ⟨a, ha⟩
  let dS : S := ⟨d, hd⟩
  let s : Q.primeCompl := ⟨dS, hdP⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) aS s, ?_⟩
  unfold s2e_fixed_prime_localization_map
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  change algebraMap C B a = algebraMap C B d * r
  rw [mul_comm]
  exact had

#print axioms s2e_exact_fixed_prime_local_descent
end HodgeLean.Foundations.Program
