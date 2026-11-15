import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every actual value of the localized fixed-function map remains fixed under compatible local pullbacks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_prime_localization_map_fixed
    (k C B G : Type*) [CommRing k] [CommRing C] [CommRing B] [Algebra k C] [Algebra C B]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (β : G → (B →+* B))
    (hβ : ∀ (g : G) (c : C), β g (algebraMap C B c) = algebraMap C B (g • c))
    (g : G) :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    ∀ t : Localization.AtPrime Q,
      β g (s2e_fixed_prime_localization_map k C B G P t) =
        s2e_fixed_prime_localization_map k C B G P t := by
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  let f := s2e_fixed_prime_localization_map k C B G P
  have he : (β g).comp f = f := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    ext a
    simp only [RingHom.comp_apply]
    change β g (s2e_fixed_prime_localization_map k C B G P (algebraMap S _ a)) =
      s2e_fixed_prime_localization_map k C B G P (algebraMap S _ a)
    rw [s2e_fixed_prime_localization_map_of, hβ, a.property g]
  exact fun t => DFunLike.congr_fun he t

#print axioms s2e_fixed_prime_localization_map_fixed
end HodgeLean.Foundations.Program
