import HodgeLean.Foundations.Program.TorusAlgebraizationB52Hermitian
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Theta
import HodgeLean.Foundations.Program.TorusAlgebraizationB52ExponentialSeries
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_inv_factor_uniform_bound
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R : ℝ) (l : Λ) (z : b5_V Λ F), ‖z‖ ≤ R →
      ‖(b5_factor Λ F hF Q l z)⁻¹‖ ≤ Real.exp
        (-c * ‖b5_lattice Λ F l‖ ^ 2 +
          (Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ * R) * ‖b5_lattice Λ F l‖) := by
  obtain ⟨c, hc, hbound⟩ := b52_H_lower_bound Λ F hF Q hpos
  refine ⟨(Real.pi / 2) * c, mul_pos (by positivity) hc, ?_⟩
  intro R l z hz
  rw [b52_norm_inv_factor]
  apply Real.exp_le_exp.mpr
  have hquad := mul_le_mul_of_nonneg_left (hbound (b5_lattice Λ F l))
    (show 0 ≤ Real.pi / 2 by positivity)
  have hcross := (neg_le_abs (b5_H Λ F hF Q (b5_lattice Λ F l) z).re).trans
    (b52_H_re_bound Λ F hF Q (b5_lattice Λ F l) z)
  have hR := mul_le_mul_of_nonneg_left hz
    (mul_nonneg (norm_nonneg (b52_H_continuousBilinear Λ F hF Q))
      (norm_nonneg (b5_lattice Λ F l)))
  have hlin := mul_le_mul_of_nonneg_left (hcross.trans hR) Real.pi_pos.le
  nlinarith

#print axioms b52_inv_factor_uniform_bound

include hF in
theorem b52_summable_coordinate_gaussian {c : ℝ} (hc : 0 < c) (B : ℝ) :
    Summable (fun l : Λ ↦ Real.exp
      (-c * ‖b5_lattice Λ F l‖ ^ 2 + B * ‖b5_lattice Λ F l‖)) := by
  haveI := b52_lattice_discrete Λ F hF
  have hi : Function.Injective (b5_lattice Λ F).rangeRestrict := by
    intro x y hxy
    exact b52_lattice_injective Λ F hF (congrArg Subtype.val hxy)
  have hs := (b52_summable_lattice_gaussian (b5_lattice Λ F).range hc B).comp_injective hi
  convert! hs using 1

#print axioms b52_summable_coordinate_gaussian

def b52_thetaExponent (l : Λ) : b5_V Λ F →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ -(Real.pi : ℂ) * b5_H Λ F hF Q (b5_lattice Λ F l) z
      map_add' := by
        intro x y
        rw [b5_H_add_right]
        ring
      map_smul' := by
        intro c z
        simp only [b5_H, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp] theorem b52_thetaExponent_apply (l : Λ) (z : b5_V Λ F) :
    b52_thetaExponent Λ F hF Q l z =
      -(Real.pi : ℂ) * b5_H Λ F hF Q (b5_lattice Λ F l) z := rfl

theorem b52_thetaExponent_norm_le (l : Λ) :
    ‖b52_thetaExponent Λ F hF Q l‖ ≤
      Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ * ‖b5_lattice Λ F l‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [b52_thetaExponent_apply, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := (b52_H_continuousBilinear Λ F hF Q).le_opNorm₂ (b5_lattice Λ F l) z
  simp only [b52_H_continuousBilinear_apply] at h
  calc
    _ ≤ Real.pi * (‖b52_H_continuousBilinear Λ F hF Q‖ * ‖b5_lattice Λ F l‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left h Real.pi_pos.le
    _ = _ := by ring

#print axioms b52_thetaExponent_norm_le

theorem b52_inv_factor_exponential (l : Λ) (z : b5_V Λ F) :
    (b5_factor Λ F hF Q l z)⁻¹ = (b5_factor Λ F hF Q l 0)⁻¹ *
      Complex.exp (b52_thetaExponent Λ F hF Q l z) := by
  have h := b5_factor_add_right Λ F hF Q l 0 z
  simp only [zero_add] at h
  rw [h]
  simp only [b52_thetaExponent_apply, neg_mul, Complex.exp_neg, mul_inv_rev, mul_comm]

#print axioms b52_inv_factor_exponential

theorem b52_theta_coefficients_summable
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re) (R : ℝ) :
    Summable (fun l : Λ ↦ ‖(b5_factor Λ F hF Q l 0)⁻¹‖ *
      Real.exp (‖b52_thetaExponent Λ F hF Q l‖ * R)) := by
  obtain ⟨c, hc, hb⟩ := b52_inv_factor_uniform_bound Λ F hF Q hpos
  apply (b52_summable_coordinate_gaussian Λ F hF hc
    (Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ * |R|)).of_norm_bounded
  intro l
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 := hb 0 l 0 (by simp)
  simp only [norm_zero, mul_zero, zero_mul, add_zero] at h0
  have ha := mul_le_mul_of_nonneg_right (b52_thetaExponent_norm_le Λ F hF Q l)
    (abs_nonneg R)
  have ha' := mul_le_mul_of_nonneg_left (le_abs_self R)
    (norm_nonneg (b52_thetaExponent Λ F hF Q l))
  calc
    _ ≤ Real.exp (-c * ‖b5_lattice Λ F l‖ ^ 2) *
        Real.exp ((Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ *
          ‖b5_lattice Λ F l‖) * |R|) :=
      mul_le_mul h0 (Real.exp_le_exp.mpr (ha'.trans ha)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms b52_theta_coefficients_summable

theorem b52_differentiable_inv_factor_sum
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re) :
    Differentiable ℂ (fun z ↦ ∑' l : Λ, (b5_factor Λ F hF Q l z)⁻¹) := by
  have heq : (fun z ↦ ∑' l : Λ, (b5_factor Λ F hF Q l z)⁻¹) =
      (fun z ↦ ∑' l : Λ, (b5_factor Λ F hF Q l 0)⁻¹ *
        Complex.exp (b52_thetaExponent Λ F hF Q l z)) := by
    funext z
    exact tsum_congr (fun l ↦ b52_inv_factor_exponential Λ F hF Q l z)
  rw [heq]
  exact b52_differentiable_exponential_series (b52_thetaExponent Λ F hF Q)
    (fun l ↦ (b5_factor Λ F hF Q l 0)⁻¹)
    (b52_theta_coefficients_summable Λ F hF Q hpos)

#print axioms b52_differentiable_inv_factor_sum

def b52_periodizedUnitSection
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z) :
    b5_sections Λ F hF Q 1 := by
  refine ⟨fun z ↦ ∑' l : Λ, (b5_factor Λ F hF Q l z)⁻¹,
    b52_differentiable_inv_factor_sum Λ F hF Q hpos, ?_⟩
  intro m z
  have hne : ∀ l z, b5_factor Λ F hF Q l z ≠ 0 := fun l z ↦
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  simpa only [b52_periodize, one_div, pow_one, LinearMap.toAddMonoidHom_coe] using
    b52_periodize_translate (b5_lattice Λ F).toAddMonoidHom
      (b5_factor Λ F hF Q) hcocycle hne (fun _ ↦ 1) m z

#print axioms b52_periodizedUnitSection

end HodgeLean.Foundations.Program
