import HodgeLean.Foundations.Program.RigidStartingSystemDefs

/-! # Derivative of the degree-six map and the pulled-back coefficient

Logarithmic derivatives of `b65r_phi` and of the fibre polynomials, and the pointwise identity
`b65r_pullback = φ' • b65r_A ∘ φ` off the poles, used by the pullback transport.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65t_P_hasDerivAt (ε s : ℂ) :
    HasDerivAt (b65r_P ε)
      (2*s*(s-3)^4 + 4*s^2*(s-3)^3 -
        ε * (3*(s-1)^2*(s+2)^3 + 3*(s-1)^3*(s+2)^2)) s := by
  convert (((hasDerivAt_id s).fun_pow 2).mul
    (((hasDerivAt_id s).sub_const 3).fun_pow 4)).sub
    ((((hasDerivAt_id s).sub_const 1).fun_pow 3).mul
      (((hasDerivAt_id s).add_const 2).fun_pow 3) |>.const_mul ε) using 1
  · funext z
    dsimp [b65r_P]
    ring
  · dsimp
    ring

theorem b65t_phi_hasDerivAt (s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2) :
    HasDerivAt b65r_phi
      (3*s*(s-3)^3*(5*s^2-3*s+4) / ((s-1)^4*(s+2)^4)) s := by
  have hd : (s-1)^3*(s+2)^3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1))
      (pow_ne_zero _ (by exact fun h ↦ hneg2 (by linear_combination h)))
  convert (((hasDerivAt_id s).fun_pow 2).mul
    (((hasDerivAt_id s).sub_const 3).fun_pow 4)).div
    ((((hasDerivAt_id s).sub_const 1).fun_pow 3).mul
      (((hasDerivAt_id s).add_const 2).fun_pow 3)) hd using 1
  · rfl
  · dsimp only [id_eq, Pi.mul_apply]
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hs2 : s + 2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
    field_simp
    <;> ring

theorem b65t_phi_sub (ε s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2) :
    b65r_phi s - ε = b65r_P ε s / ((s-1)^3*(s+2)^3) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : s + 2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
  dsimp [b65r_phi, b65r_P]
  field_simp
  <;> ring

theorem b65t_phi_logDeriv (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (hneg2 : s ≠ -2) :
    deriv b65r_phi s * (b65r_phi s)⁻¹ =
      2/s + 4/(s-3) - (3/(s-1) + 3/(s+2)) := by
  rw [(b65t_phi_hasDerivAt s h1 hneg2).deriv]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : s + 2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
  have hs3 : s - 3 ≠ 0 := sub_ne_zero.mpr h3
  dsimp [b65r_phi]
  field_simp
  <;> ring

theorem b65t_phi_fibre_logDeriv (ε s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (hP : b65r_P ε s ≠ 0) :
    deriv b65r_phi s * (b65r_phi s - ε)⁻¹ =
      deriv (b65r_P ε) s / b65r_P ε s - (3/(s-1) + 3/(s+2)) := by
  rw [(b65t_phi_hasDerivAt s h1 hneg2).deriv,
    (b65t_P_hasDerivAt ε s).deriv, b65t_phi_sub ε s h1 hneg2]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : s + 2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
  field_simp
  dsimp [b65r_P]
  ring

theorem b65t_operator_Binf : b65r_operator b65r_Binf =
    -(b65r_operator b65r_B0 + b65r_operator b65r_B5 + b65r_operator b65r_Bneg7) := by
  ext v i
  change (-(b65r_B0 + b65r_B5 + b65r_Bneg7)).mulVec v i =
    -((b65r_B0.mulVec v i + b65r_B5.mulVec v i) + b65r_Bneg7.mulVec v i)
  simp only [Matrix.neg_mulVec, Matrix.add_mulVec, Pi.neg_apply, Pi.add_apply]

theorem b65t_pullback_formula (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (hneg7 : b65r_P (-7) s ≠ 0) :
    b65r_pullback s = deriv b65r_phi s • b65r_A (b65r_phi s) := by
  unfold b65r_pullback b65r_A
  rw [show b65r_phi s + 7 = b65r_phi s - (-7) by ring, b65t_operator_Binf]
  simp only [smul_add, smul_neg, smul_smul]
  rw [b65t_phi_logDeriv s h0 h3 h1 hneg2,
    b65t_phi_fibre_logDeriv 5 s h1 hneg2 h5,
    b65t_phi_fibre_logDeriv (-7) s h1 hneg2 hneg7]
  module

end HodgeLean.Foundations.Program
