import HodgeLean.Foundations.Program.TorusAlgebraizationB52Uniform

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_seed_coefficients_summable
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (A : b5_V Λ F →L[ℂ] ℂ) (R : ℝ) :
    Summable (fun l : Λ ↦
      ‖(b5_factor Λ F hF Q l 0)⁻¹ * Complex.exp (A (b5_lattice Λ F l))‖ *
        Real.exp (‖b52_thetaExponent Λ F hF Q l‖ * R)) := by
  obtain ⟨c, hc, hb⟩ := b52_inv_factor_uniform_bound Λ F hF Q hpos
  apply (b52_summable_coordinate_gaussian Λ F hF hc
    (‖A‖ + Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ * |R|)).of_norm_bounded
  intro l
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_exp,
    mul_assoc, ← Real.exp_add]
  have h0 := hb 0 l 0 (by simp)
  simp only [mul_zero, zero_mul, add_zero] at h0
  have ha := mul_le_mul_of_nonneg_right (b52_thetaExponent_norm_le Λ F hF Q l)
    (abs_nonneg R)
  have ha' := mul_le_mul_of_nonneg_left (le_abs_self R)
    (norm_nonneg (b52_thetaExponent Λ F hF Q l))
  have hseed := (Complex.re_le_norm (A (b5_lattice Λ F l))).trans
    (A.le_opNorm (b5_lattice Λ F l))
  calc
    _ ≤ Real.exp (-c * ‖b5_lattice Λ F l‖ ^ 2) *
        Real.exp (‖A‖ * ‖b5_lattice Λ F l‖ +
          (Real.pi * ‖b52_H_continuousBilinear Λ F hF Q‖ *
            ‖b5_lattice Λ F l‖) * |R|) :=
      mul_le_mul h0 (Real.exp_le_exp.mpr (add_le_add hseed (ha'.trans ha)))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms b52_seed_coefficients_summable

theorem b52_periodize_exponential_eq (A : b5_V Λ F →L[ℂ] ℂ) (z : b5_V Λ F) :
    b52_periodize (b5_lattice Λ F).toAddMonoidHom (b5_factor Λ F hF Q)
      (fun w ↦ Complex.exp (A w)) z =
      Complex.exp (A z) * ∑' l : Λ,
        ((b5_factor Λ F hF Q l 0)⁻¹ * Complex.exp (A (b5_lattice Λ F l))) *
          Complex.exp (b52_thetaExponent Λ F hF Q l z) := by
  unfold b52_periodize
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  change Complex.exp (A (z + b5_lattice Λ F l)) / b5_factor Λ F hF Q l z = _
  rw [map_add, Complex.exp_add, div_eq_mul_inv, b52_inv_factor_exponential]
  ring

#print axioms b52_periodize_exponential_eq

theorem b52_differentiable_exponential_periodization
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (A : b5_V Λ F →L[ℂ] ℂ) :
    Differentiable ℂ (b52_periodize (b5_lattice Λ F).toAddMonoidHom
      (b5_factor Λ F hF Q) (fun w ↦ Complex.exp (A w))) := by
  have hd := A.differentiable.cexp.mul
    (b52_differentiable_exponential_series (b52_thetaExponent Λ F hF Q)
      (fun l ↦ (b5_factor Λ F hF Q l 0)⁻¹ * Complex.exp (A (b5_lattice Λ F l)))
      (b52_seed_coefficients_summable Λ F hF Q hpos A))
  convert hd using 1
  funext z
  exact b52_periodize_exponential_eq Λ F hF Q A z

#print axioms b52_differentiable_exponential_periodization

def b52_exponentialSeedSection
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (A : b5_V Λ F →L[ℂ] ℂ) : b5_sections Λ F hF Q 1 := by
  refine ⟨b52_periodize (b5_lattice Λ F).toAddMonoidHom
    (b5_factor Λ F hF Q) (fun w ↦ Complex.exp (A w)),
    b52_differentiable_exponential_periodization Λ F hF Q hpos A, ?_⟩
  intro m z
  have hne : ∀ l z, b5_factor Λ F hF Q l z ≠ 0 := fun l z ↦
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  simpa only [pow_one, LinearMap.toAddMonoidHom_coe] using
    b52_periodize_translate (b5_lattice Λ F).toAddMonoidHom
      (b5_factor Λ F hF Q) hcocycle hne (fun w ↦ Complex.exp (A w)) m z

#print axioms b52_exponentialSeedSection

end HodgeLean.Foundations.Program
