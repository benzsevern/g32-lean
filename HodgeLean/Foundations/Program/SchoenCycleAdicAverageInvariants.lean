import HodgeLean.Foundations.Program.SchoenCycleAdicFixedSplitting
import HodgeLean.Foundations.Program.SchoenCycleAverageFixedSubmodule
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Adic completion of simultaneous invariants under averaging -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Normalized averaging identifies the completion of simultaneous invariants with simultaneous invariants in the completion.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, averaging projections. -/
def s2e_adic_average_invariants_equiv
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype G]
    (I : Ideal R) (a : G → M →ₗ[R] M) (c : R)
    (hc : c * (Fintype.card G : R) = 1)
    (p : M →ₗ[R] M) (hsum : p = c • ∑ g, a g)
    (hap : ∀ g, (a g).comp p = p) :
    AdicCompletion I (⨅ g, (a g).fixedSubmodule : Submodule R M) ≃ₗ[AdicCompletion I R]
      (⨅ g, (AdicCompletion.map I (a g)).fixedSubmodule :
        Submodule (AdicCompletion I R) (AdicCompletion I M)) := by
  classical
  have hp : p.comp p = p := by
    calc
      p.comp p = (c • ∑ g, a g).comp p := congrArg (fun f => f.comp p) hsum
      _ = c • ∑ g, (a g).comp p := by
        ext x
        simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply]
      _ = c • ∑ _ : G, p := by simp only [hap]
      _ = p := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R,
          smul_smul, hc, one_smul]
  have hsrc := s2e_average_fixed_submodule a c hc p hsum hap
  have hsumhat : AdicCompletion.map I p =
      algebraMap R (AdicCompletion I R) c • ∑ g, AdicCompletion.map I (a g) := by
    simpa only [map_smul, map_sum, IsScalarTower.algebraMap_smul] using
      congrArg (AdicCompletion.map I) hsum
  have haphat (g : G) :
      (AdicCompletion.map I (a g)).comp (AdicCompletion.map I p) = AdicCompletion.map I p := by
    rw [AdicCompletion.map_comp, hap g]
  have hchat : algebraMap R (AdicCompletion I R) c * (Fintype.card G : AdicCompletion I R) = 1 := by
    rw [← map_natCast (algebraMap R (AdicCompletion I R)), ← map_mul, hc, map_one]
  have hdst := s2e_average_fixed_submodule (fun g => AdicCompletion.map I (a g))
    (algebraMap R (AdicCompletion I R) c) hchat (AdicCompletion.map I p) hsumhat haphat
  exact (AdicCompletion.congr I (LinearEquiv.ofEq _ _ hsrc.symm)).trans
    ((s2e_adic_fixed_submodule_equiv I p hp).trans (LinearEquiv.ofEq _ _ hdst))

#print axioms s2e_adic_average_invariants_equiv
end HodgeLean.Foundations.Program
