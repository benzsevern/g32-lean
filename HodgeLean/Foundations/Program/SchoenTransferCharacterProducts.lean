import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace HodgeLean.Foundations.Program

/-- A bilinear invariant pairing vanishes between equal characters whose square is nontrivial. -/
theorem invariant_bilinear_equal_character_zero {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (B : M →ₗ[K] M →ₗ[K] N) (A : Module.End K M) (c : K)
    (hc : c * c ≠ 1) (hB : ∀ x y, B (A x) (A y) = B x y)
    {x y : M} (hx : A x = c • x) (hy : A y = c • y) : B x y = 0 := by
  have h : (c * c - 1) • B x y = 0 := by
    rw [sub_smul, one_smul, ← smul_smul]
    have he := hB x y
    simp only [hx, hy, map_smul, LinearMap.smul_apply] at he
    exact sub_eq_zero.mpr he
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)

/-- The square of a primitive character of order at least three differs from one. -/
theorem primitive_character_square_ne_one {K : Type*} [Field K] {c : K} {m : ℕ}
    (h : IsPrimitiveRoot c m) (hm : 3 ≤ m) : c * c ≠ 1 := by
  simpa only [pow_two] using h.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0)
    (by omega : 2 < m)

end HodgeLean.Foundations.Program
