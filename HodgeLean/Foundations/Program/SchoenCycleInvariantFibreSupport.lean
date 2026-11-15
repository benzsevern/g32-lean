import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Every prime containing the actual extended maximal fibre ideal belongs to the retained prime's finite group orbit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_fibre_prime_orbit
    (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsMaximal] (I : Ideal B) [I.IsPrime] [I.LiesOver p]
    (Q : Ideal B) [Q.IsPrime] (hQ : p.map (algebraMap A B) ≤ Q) :
    ∃ g : G, Q = g • I := by
  have hle : p ≤ Q.under A := Ideal.map_le_iff_le_comap.mp hQ
  have hEq : Q.under A = p :=
    ((Ideal.IsMaximal.eq_of_le (inferInstance : p.IsMaximal)
      (Ideal.IsPrime.ne_top (inferInstance : (Q.under A).IsPrime)) hle)).symm
  apply Algebra.IsInvariant.exists_smul_of_under_eq A B G I Q
  exact (Ideal.over_def I p).symm.trans hEq.symm

end HodgeLean.Foundations.Program
