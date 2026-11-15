import HodgeLean.Foundations.Program.SchoenCycleAdicAverageInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The averaging comparison has the canonical inclusion as its underlying map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_adic_average_invariants_val
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype G]
    (I : Ideal R) (a : G → M →ₗ[R] M) (c : R)
    (hc : c * (Fintype.card G : R) = 1)
    (p : M →ₗ[R] M) (hsum : p = c • ∑ g, a g)
    (hap : ∀ g, (a g).comp p = p)
    (x : AdicCompletion I (⨅ g, (a g).fixedSubmodule : Submodule R M)) :
    (s2e_adic_average_invariants_equiv I a c hc p hsum hap x).val =
      AdicCompletion.map I (⨅ g, (a g).fixedSubmodule : Submodule R M).subtype x := by
  unfold s2e_adic_average_invariants_equiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    AdicCompletion.congr_apply]
  change AdicCompletion.map I _ (AdicCompletion.map I _ x) = _
  rw [AdicCompletion.map_comp_apply]
  congr 1

#print axioms s2e_adic_average_invariants_val
end HodgeLean.Foundations.Program
