import HodgeLean.Foundations.Abdulali.QuaternionSplit
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion
namespace HodgeLean.Foundations.Abdulali

/-- Every nonzero rational quaternion in this definite presentation is a unit.
Source: Mumford, Abelian Varieties, §19, definite quaternion endomorphism algebras;
the inverse is the conjugate divided by the positive reduced norm. -/
theorem definiteQuaternion_isUnit (b : ℚ) (hb : b < 0)
    (q : ℍ[ℚ, -3, 0, b]) (hq : q ≠ 0) : IsUnit q := by
  let N := q.re ^ 2 + 3 * q.imI ^ 2 - b * q.imJ ^ 2 - 3 * b * q.imK ^ 2
  have hN : N ≠ 0 := by
    intro h
    have h0 : q.re ^ 2 + 3 * q.imI ^ 2 + (-b) * q.imJ ^ 2 +
        (-3*b) * q.imK ^ 2 = 0 := by dsimp [N] at h; linarith
    have h1 : q.re = 0 := by
      nlinarith [sq_nonneg q.imI,
        mul_nonneg (le_of_lt (neg_pos.mpr hb)) (sq_nonneg q.imJ),
        mul_nonneg (show 0 ≤ -3*b by linarith) (sq_nonneg q.imK)]
    have h2 : q.imI = 0 := by
      nlinarith [sq_nonneg q.re,
        mul_nonneg (le_of_lt (neg_pos.mpr hb)) (sq_nonneg q.imJ),
        mul_nonneg (show 0 ≤ -3*b by linarith) (sq_nonneg q.imK)]
    have h3 : q.imJ = 0 := by
      have : (-b) * q.imJ ^ 2 = 0 := by
        nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
          mul_nonneg (show 0 ≤ -3*b by linarith) (sq_nonneg q.imK)]
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (mul_eq_zero.mp this |>.resolve_left (ne_of_gt (neg_pos.mpr hb)))
    have h4 : q.imK = 0 := by
      have : (-3*b) * q.imK ^ 2 = 0 := by
        nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
          mul_nonneg (le_of_lt (neg_pos.mpr hb)) (sq_nonneg q.imJ)]
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (mul_eq_zero.mp this |>.resolve_left (by linarith))
    apply hq
    ext <;> assumption
  refine ⟨⟨q, N⁻¹ • star q, ?_, ?_⟩, rfl⟩
  · ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_smul,
      QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
      QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, smul_eq_mul] <;>
      field_simp [hN] <;> dsimp [N] <;> ring
  · ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_smul,
      QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
      QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, smul_eq_mul] <;>
      field_simp [hN] <;> dsimp [N] <;> ring

#print axioms definiteQuaternion_isUnit
end HodgeLean.Foundations.Abdulali
