import HodgeLean.Foundations.Program.SchoenCycleAdicAverageInvariants
import Mathlib.Basic.Complex.Basic

/-! # Adic completion and finite complex group invariants -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Finite-group invariant modules over a complex algebra commute with adic completion.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, finite-group invariants. -/
def s2e_adic_finite_group_invariants_equiv
    {R M G : Type*} [CommRing R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Group G] [Fintype G]
    (I : Ideal R) (a : G →* (M ≃ₗ[R] M)) :
    AdicCompletion I (⨅ g, (a g).toLinearMap.fixedSubmodule : Submodule R M) ≃ₗ[AdicCompletion I R]
      (⨅ g, (AdicCompletion.map I (a g).toLinearMap).fixedSubmodule :
        Submodule (AdicCompletion I R) (AdicCompletion I M)) := by
  classical
  let c : R := algebraMap ℂ R ((Fintype.card G : ℂ)⁻¹)
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : c * (Fintype.card G : R) = 1 := by
    dsimp only [c]
    rw [← map_natCast (algebraMap ℂ R), ← map_mul, inv_mul_cancel₀ hn, map_one]
  let p : M →ₗ[R] M := c • ∑ g, (a g).toLinearMap
  have hap (g : G) : (a g).toLinearMap.comp p = p := by
    ext x
    simp only [p, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearEquiv.coe_coe, map_smul, map_sum]
    congr 1
    simp only [← LinearEquiv.mul_apply, ← map_mul]
    rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => a h x)]
  exact s2e_adic_average_invariants_equiv I (fun g => (a g).toLinearMap) c hc p rfl hap

#print axioms s2e_adic_finite_group_invariants_equiv
end HodgeLean.Foundations.Program
