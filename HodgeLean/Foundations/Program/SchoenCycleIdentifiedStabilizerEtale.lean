import HodgeLean.Foundations.Program.SchoenCycleStabilizerAugmentedEtale

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- An identified geometric stabilizer has the same augmented etale fixed-function algebra as the actual prime stabilizer.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1; EGA IV, 17.6.1. -/
theorem s2e_fixed_function_etale_of_stabilizer_eq
    (A C G : Type*) [CommRing A] [Algebra ℂ A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Finite A C]
    [Group G] [Fintype G] [MulSemiringAction G C]
    [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hinj : Function.Injective (algebraMap A C)) (P : Ideal C) [P.IsMaximal]
    (H : Subgroup G)
    (hH : H = MulAction.stabilizer G
      (⟨P, MulAction.mem_orbit_self P⟩ : MulAction.orbit G P)) :
    let S := FixedPoints.subalgebra A C H
    letI : Algebra ℂ S := ((algebraMap A S).comp (algebraMap ℂ A)).toAlgebra
    ∀ ε : Localization.AtPrime (P.under S) →ₐ[ℂ] ℂ,
      Algebra.IsEtaleAt A (P.under S) := by
  subst H
  exact s2e_prime_stabilizer_fixed_function_etale A C G hinj P

#print axioms s2e_fixed_function_etale_of_stabilizer_eq
end HodgeLean.Foundations.Program
