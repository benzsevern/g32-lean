import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual map from the localization of a fixed-function algebra to the original prime localization.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_fixed_prime_localization_map
    (k C B G : Type*) [CommRing k] [CommRing C] [CommRing B] [Algebra k C] [Algebra C B]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P] :
    let S := FixedPoints.subalgebra k C G
    let Q := P.comap S.val.toRingHom
    Localization.AtPrime Q →+* B := by
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  let f : S →+* B := (algebraMap C B).comp S.val.toRingHom
  apply IsLocalization.lift (M := Q.primeCompl) (S := Localization.AtPrime Q) (g := f)
  intro s
  change IsUnit (algebraMap C B s.val.val)
  exact (IsLocalization.AtPrime.isUnit_to_map_iff B P s.val.val).mpr s.property

#print axioms s2e_fixed_prime_localization_map

/-- The fixed prime localization map retains the actual original value of every fixed function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_prime_localization_map_of
    (k C B G : Type*) [CommRing k] [CommRing C] [CommRing B] [Algebra k C] [Algebra C B]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (a : FixedPoints.subalgebra k C G) :
    s2e_fixed_prime_localization_map k C B G P
      (algebraMap (FixedPoints.subalgebra k C G)
        (Localization.AtPrime (P.comap (FixedPoints.subalgebra k C G).val.toRingHom)) a) =
      algebraMap C B a.val := by
  unfold s2e_fixed_prime_localization_map
  exact IsLocalization.lift_eq _ a

#print axioms s2e_fixed_prime_localization_map_of
end HodgeLean.Foundations.Program
