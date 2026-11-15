import HodgeLean.Foundations.Program.SchoenCycleAdicInvariantBase
import HodgeLean.Foundations.Program.SchoenCycleAdicGroupNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The invariant base comparison is induced by the original algebra structure map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_adic_invariant_base_val
    {R B G : Type*} [CommRing R] [Algebra ℂ R] [CommRing B] [Algebra R B]
    [Group G] [Fintype G] (I : Ideal R) (a : G →* (B ≃ₐ[R] B))
    (hinj : Function.Injective (algebraMap R B))
    (hdescent : ∀ b : B, (∀ g, a g b = b) → ∃ r : R, algebraMap R B r = b)
    (x : AdicCompletion I R) :
    (s2e_adic_invariant_base_equiv I a hinj hdescent x).val =
      AdicCompletion.map I (Algebra.linearMap R B) x := by
  unfold s2e_adic_invariant_base_equiv
  simp only [LinearEquiv.trans_apply]
  refine (s2e_adic_finite_group_invariants_val I _ _).trans ?_
  rw [AdicCompletion.congr_apply]
  refine (AdicCompletion.map_comp_apply I _ _ x).trans ?_
  rfl

#print axioms s2e_adic_invariant_base_val
end HodgeLean.Foundations.Program
