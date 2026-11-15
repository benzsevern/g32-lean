import HodgeLean.Foundations.Program.PrymVariationCentreHomology
import HodgeLean.Foundations.Program.PrymVariationLattice

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def b63d_scalarBlock0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -((2 * g32h_omega + 1) / 3), (1 - g32h_omega) / 3, (g32h_omega + 2) / 3;
     0, (g32h_omega - 1) / 3, (2 * g32h_omega + 1) / 3, (g32h_omega + 2) / 3;
     0, (g32h_omega + 2) / 3, -((g32h_omega + 2) / 3), (g32h_omega + 2) / 3;
     -1, 0, 0, 0]

set_option maxHeartbeats 400000 in
theorem b63d_scalarBlock0_eq : g32R1 g32h_omega * g32X g32h_omega * g32R2 g32h_omega =
    b63d_scalarBlock0 := by
  have hw := g32h_omega_sq_add
  have hc : g32h_omega ^ 3 = 1 := by
    linear_combination (g32h_omega - 1) * hw
  have hs : g32h_omega ^ 2 = -g32h_omega - 1 := by
    linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63d_scalarBlock0, g32R1, g32R2, g32X, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    field_simp <;> ring_nf
  all_goals try rw [hc]
  all_goals try rw [hs]
  all_goals ring

def b63d_scalarBlock1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -((g32h_omega + 2) / 3), -((2 * g32h_omega + 1) / 3), (2 * g32h_omega + 1) / 3;
     (g32h_omega - 1) / 3, -((g32h_omega + 2) / 3), 0, -((2 * g32h_omega + 1) / 3);
     (2 * g32h_omega + 1) / 3, (1 - g32h_omega) / 3, -((g32h_omega + 2) / 3), 0;
     (g32h_omega - 1) / 3, 0, (2 * g32h_omega + 1) / 3, (2 * g32h_omega + 1) / 3]

def b63d_scalarBlock2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-((g32h_omega + 2) / 3), 0, -((2 * g32h_omega + 1) / 3), (g32h_omega + 2) / 3;
     0, -((g32h_omega + 2) / 3), (g32h_omega + 2) / 3, (1 - g32h_omega) / 3;
     (g32h_omega - 1) / 3, (g32h_omega + 2) / 3, (g32h_omega + 2) / 3, 0;
     (g32h_omega - 1) / 3, -((g32h_omega + 2) / 3), 0, (g32h_omega - 1) / 3]

def b63d_scalarBlock3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-1, 0, 0, 0;
     0, -((g32h_omega + 2) / 3), (g32h_omega + 2) / 3, (1 - g32h_omega) / 3;
     0, (g32h_omega + 2) / 3, (1 - g32h_omega) / 3, (g32h_omega + 2) / 3;
     0, -((g32h_omega + 2) / 3), -((2 * g32h_omega + 1) / 3), (2 * g32h_omega + 1) / 3]

set_option maxHeartbeats 400000 in
theorem b63d_scalarBlock1_eq : g32R2 g32h_omega * g32X g32h_omega * g32R2 g32h_omega =
    b63d_scalarBlock1 := by
  have hw := g32h_omega_sq_add
  have hc : g32h_omega ^ 3 = 1 := by linear_combination (g32h_omega - 1) * hw
  have hs : g32h_omega ^ 2 = -g32h_omega - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63d_scalarBlock1, g32R2, g32X, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring_nf
  all_goals try rw [hc]
  all_goals try rw [hs]
  all_goals ring

set_option maxHeartbeats 400000 in
theorem b63d_scalarBlock2_eq : g32R2 g32h_omega * g32Y g32h_omega * g32Y g32h_omega =
    b63d_scalarBlock2 := by
  have hw := g32h_omega_sq_add
  have hc : g32h_omega ^ 3 = 1 := by linear_combination (g32h_omega - 1) * hw
  have hs : g32h_omega ^ 2 = -g32h_omega - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63d_scalarBlock2, g32R2, g32Y, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring_nf
  all_goals try rw [hc]
  all_goals try rw [hs]
  all_goals ring

set_option maxHeartbeats 400000 in
theorem b63d_scalarBlock3_eq : g32R1 g32h_omega * g32X g32h_omega * g32Y g32h_omega *
    g32X g32h_omega = b63d_scalarBlock3 := by
  have hw := g32h_omega_sq_add
  have hc : g32h_omega ^ 3 = 1 := by linear_combination (g32h_omega - 1) * hw
  have hs : g32h_omega ^ 2 = -g32h_omega - 1 := by linear_combination hw
  have h4 : g32h_omega ^ 4 = g32h_omega := by
    rw [show (4 : ℕ) = 3 + 1 by omega, pow_succ, hc, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63d_scalarBlock3, g32R1, g32X, g32Y, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring_nf
  all_goals try rw [hc]
  all_goals try rw [h4]
  all_goals try rw [hs]
  all_goals ring

set_option maxHeartbeats 400000 in
theorem b63d_scalarBlocks_mul : b63d_scalarBlock0 * b63d_scalarBlock1 * b63d_scalarBlock2 *
    b63d_scalarBlock3 = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hw := g32h_omega_sq_add
  have hc : g32h_omega ^ 3 = 1 := by linear_combination (g32h_omega - 1) * hw
  have hs : g32h_omega ^ 2 = -g32h_omega - 1 := by linear_combination hw
  have h4 : g32h_omega ^ 4 = g32h_omega := by
    rw [show (4 : ℕ) = 3 + 1 by omega, pow_succ, hc, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b63d_scalarBlock0, b63d_scalarBlock1, b63d_scalarBlock2, b63d_scalarBlock3,
      Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring_nf
  all_goals try rw [hc]
  all_goals try rw [h4]
  all_goals try rw [hs]
  all_goals ring

def b63d_scalarElement : b4b_Group :=
  b4b_generators 0 * b4b_generators 2 * b4b_generators 1 * b4b_generators 1 *
    b4b_generators 2 * b4b_generators 1 * b4b_generators 1 * b4b_generators 3 *
    b4b_generators 3 * b4b_generators 0 * b4b_generators 2 * b4b_generators 3 *
    b4b_generators 2

theorem b63d_scalarElement_matrix :
    b4b_toMatrix b63d_scalarElement =
      g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  change g32R1 g32h_omega * g32X g32h_omega * g32R2 g32h_omega *
    g32R2 g32h_omega * g32X g32h_omega * g32R2 g32h_omega *
    g32R2 g32h_omega * g32Y g32h_omega * g32Y g32h_omega *
    g32R1 g32h_omega * g32X g32h_omega * g32Y g32h_omega *
    g32X g32h_omega = _
  calc
    _ = (g32R1 g32h_omega * g32X g32h_omega * g32R2 g32h_omega) *
        (g32R2 g32h_omega * g32X g32h_omega * g32R2 g32h_omega) *
        (g32R2 g32h_omega * g32Y g32h_omega * g32Y g32h_omega) *
        (g32R1 g32h_omega * g32X g32h_omega * g32Y g32h_omega *
          g32X g32h_omega) := by noncomm_ring
    _ = b63d_scalarBlock0 * b63d_scalarBlock1 * b63d_scalarBlock2 *
        b63d_scalarBlock3 := by
          rw [b63d_scalarBlock0_eq, b63d_scalarBlock1_eq, b63d_scalarBlock2_eq,
            b63d_scalarBlock3_eq]
    _ = _ := b63d_scalarBlocks_mul

theorem b63d_scalarElement_cube : b63d_scalarElement ^ 3 = 1 := by
  have hc : g32h_omega ^ 3 = 1 := by
    linear_combination (g32h_omega - 1) * g32h_omega_sq_add
  apply Subtype.val_injective
  change b4b_toMatrix (b63d_scalarElement ^ 3) = b4b_toMatrix 1
  rw [map_pow, b63d_scalarElement_matrix]
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    calc
      g32h_omega * (g32h_omega * g32h_omega) = g32h_omega ^ 3 := by ring
      _ = 1 := hc

theorem b63d_projectorCoeff_scalar (h : b4b_Group) :
    b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h +
      b4b_projectorCoeff (b63d_scalarElement * h) = 0 := by
  have hzinv : b63d_scalarElement⁻¹ = b63d_scalarElement ^ 2 := by
    calc
      b63d_scalarElement⁻¹ = b63d_scalarElement⁻¹ * 1 := by simp
      _ = b63d_scalarElement⁻¹ * b63d_scalarElement ^ 3 := by
        rw [b63d_scalarElement_cube]
      _ = b63d_scalarElement ^ 2 := by group
  have hm1 : b4b_toMatrix ((b63d_scalarElement⁻¹ * h)⁻¹) 0 0 =
      b4b_toMatrix h⁻¹ 0 0 * g32h_omega := by
    rw [mul_inv_rev, inv_inv, map_mul, b63d_scalarElement_matrix]
    simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hm2 : b4b_toMatrix ((b63d_scalarElement * h)⁻¹) 0 0 =
      b4b_toMatrix h⁻¹ 0 0 * g32h_omega ^ 2 := by
    rw [mul_inv_rev, hzinv, map_mul, map_pow, b63d_scalarElement_matrix]
    simp [Matrix.mul_apply, Fin.sum_univ_four, pow_two]
  have ha : b4b_toMatrix h⁻¹ 0 0 * g32h_omega + b4b_toMatrix h⁻¹ 0 0 +
      b4b_toMatrix h⁻¹ 0 0 * g32h_omega ^ 2 = 0 := by
    linear_combination b4b_toMatrix h⁻¹ 0 0 * g32h_omega_sq_add
  have har := congrArg Complex.re ha
  simp only [Complex.add_re, Complex.zero_re] at har
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  rw [Int.cast_add, Int.cast_add, Int.cast_zero, b63l_projectorCoeff_cast,
    b63l_projectorCoeff_cast, b63l_projectorCoeff_cast, hm1, hm2]
  linear_combination 6 * har

end HodgeLean.Foundations.Program
