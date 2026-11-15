import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Algebra.Algebra.Basic

/-! # Fixed submodules of normalized averaging projections -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A normalized averaging projection has precisely the simultaneous fixed vectors.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, averaging projections. -/
theorem s2e_average_fixed_submodule
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype G]
    (a : G → M →ₗ[R] M) (c : R) (hc : c * (Fintype.card G : R) = 1)
    (p : M →ₗ[R] M) (hsum : p = c • ∑ g, a g)
    (hap : ∀ g, (a g).comp p = p) :
    p.fixedSubmodule = ⨅ g, (a g).fixedSubmodule := by
  classical
  ext x
  simp only [LinearMap.mem_fixedSubmodule_iff, Submodule.mem_iInf]
  constructor
  · intro hx g
    calc
      a g x = a g (p x) := congrArg (a g) hx.symm
      _ = p x := DFunLike.congr_fun (hap g) x
      _ = x := hx
  · intro hx
    rw [hsum]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, hx]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R,
      smul_smul, hc, one_smul]

#print axioms s2e_average_fixed_submodule
end HodgeLean.Foundations.Program
