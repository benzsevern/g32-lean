import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual fixed-prime localization map preserves its prescribed scalar algebra structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_fixed_prime_localization_algHom
    (k C B G : Type*) [CommRing k] [CommRing C] [CommRing B]
    [Algebra k C] [Algebra C B] [Algebra k B] [IsScalarTower k C B]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P] :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    Localization.AtPrime Q →ₐ[k] B := by
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  refine ⟨s2e_fixed_prime_localization_map k C B G P, ?_⟩
  intro a
  change s2e_fixed_prime_localization_map k C B G P
    (algebraMap k (Localization.AtPrime Q) a) = algebraMap k B a
  rw [IsScalarTower.algebraMap_apply k S (Localization.AtPrime Q), s2e_fixed_prime_localization_map_of]
  exact (IsScalarTower.algebraMap_apply k C B a).symm

#print axioms s2e_fixed_prime_localization_algHom
end HodgeLean.Foundations.Program
