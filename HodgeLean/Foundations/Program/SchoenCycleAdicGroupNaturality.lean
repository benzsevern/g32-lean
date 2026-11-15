import HodgeLean.Foundations.Program.SchoenCycleAdicGroupInvariants
import HodgeLean.Foundations.Program.SchoenCycleAdicAverageNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The finite-group comparison retains the canonical inclusion on adic modules.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_adic_finite_group_invariants_val
    {R M G : Type*} [CommRing R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Group G] [Fintype G]
    (I : Ideal R) (a : G →* (M ≃ₗ[R] M))
    (x : AdicCompletion I (⨅ g, (a g).toLinearMap.fixedSubmodule : Submodule R M)) :
    (s2e_adic_finite_group_invariants_equiv I a x).val =
      AdicCompletion.map I (⨅ g, (a g).toLinearMap.fixedSubmodule : Submodule R M).subtype x := by
  unfold s2e_adic_finite_group_invariants_equiv
  exact s2e_adic_average_invariants_val ..

#print axioms s2e_adic_finite_group_invariants_val
end HodgeLean.Foundations.Program
