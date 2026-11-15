import HodgeLean.Foundations.Program.TorusAlgebraizationB52Characters
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Separation

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

include hF in
theorem b52_real_linear_ext_lattice {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (L M : b5_V Λ F →ₗ[ℝ] W)
    (h : ∀ l, L (b5_lattice Λ F l) = M (b5_lattice Λ F l)) : L = M := by
  obtain ⟨b, hb⟩ := b2_latticeMap_basis_aux (Module.finBasis ℤ Λ) F hF
  apply (b.map ((b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).restrictScalars ℝ)).ext
  intro i
  change L (b2_coord _ (b i)) = M (b2_coord _ (b i))
  rw [hb i]
  exact h ((Module.finBasis ℤ Λ) i)

theorem b52_H_smul_left (a : ℂ) (x y : b5_V Λ F) :
    b5_H Λ F hF Q (a • x) y = star a * b5_H Λ F hF Q x y := by
  simp only [b5_H, map_smul, b2a_conj_smul, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

theorem b52_H_not_linear_on_lattice
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (v : b5_V Λ F) (hv : v ≠ 0) (L : b5_V Λ F →ₗ[ℂ] ℂ) :
    ∃ l, L (b5_lattice Λ F l) ≠ b5_H Λ F hF Q (b5_lattice Λ F l) v := by
  by_contra hn
  have h : ∀ l, L (b5_lattice Λ F l) = b5_H Λ F hF Q (b5_lattice Λ F l) v := by
    simpa only [not_exists, not_not] using hn
  have heq := b52_real_linear_ext_lattice Λ F hF (L.restrictScalars ℝ)
    ((b52_H_continuousBilinear Λ F hF Q).flip v).toLinearMap h
  have heval : ∀ z, L z = b5_H Λ F hF Q z v := fun z ↦ LinearMap.congr_fun heq z
  have hi := heval (Complex.I • v)
  simp only [map_smul, smul_eq_mul, b52_H_smul_left, Complex.star_def,
    Complex.conj_I, heval v] at hi
  have hz : b5_H Λ F hF Q v v = 0 := by
    apply (mul_eq_zero.mp (show Complex.I * b5_H Λ F hF Q v v = 0 from ?_)).resolve_left
      Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * hi
  have hp := hpos v hv
  simp [hz] at hp

theorem b52_factor_hasFDerivAt (l : Λ) (z : b5_V Λ F) :
    HasFDerivAt (b5_factor Λ F hF Q l)
      ((b5_factor Λ F hF Q l z) • (-b52_thetaExponent Λ F hF Q l)) z := by
  have hf : ∀ w, b5_factor Λ F hF Q l w = b5_factor Λ F hF Q l 0 *
      Complex.exp ((-b52_thetaExponent Λ F hF Q l) w) := by
    intro w
    simpa only [zero_add, ContinuousLinearMap.neg_apply, b52_thetaExponent_apply,
      neg_mul, neg_neg] using b5_factor_add_right Λ F hF Q l 0 w
  have hd : HasFDerivAt
      (fun w ↦ b5_factor Λ F hF Q l 0 *
        Complex.exp ((-b52_thetaExponent Λ F hF Q l) w))
      ((b5_factor Λ F hF Q l 0 * Complex.exp ((-b52_thetaExponent Λ F hF Q l) z)) •
        (-b52_thetaExponent Λ F hF Q l)) z := by
    simpa only [smul_smul] using
      ((-b52_thetaExponent Λ F hF Q l).hasFDerivAt.cexp.const_mul
        (b5_factor Λ F hF Q l 0))
  convert hd using 1
  · exact funext hf
  · rw [hf z]

theorem b52_section_fderiv_translate (s : b5_sections Λ F hF Q 1)
    (l : Λ) (z v : b5_V Λ F) :
    fderiv ℂ s.val (z + b5_lattice Λ F l) v = b5_factor Λ F hF Q l z *
      (fderiv ℂ s.val z v + (Real.pi : ℂ) *
        b5_H Λ F hF Q (b5_lattice Λ F l) v * s.val z) := by
  have hl := (s.property.1 (z + b5_lattice Λ F l)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).add_const (b5_lattice Λ F l))
  have hr := (b52_factor_hasFDerivAt Λ F hF Q l z).mul (s.property.1 z).hasFDerivAt
  have he : (fun x ↦ s.val (x + b5_lattice Λ F l)) =
      (fun x ↦ b5_factor Λ F hF Q l x * s.val x) := by
    funext x
    simpa only [pow_one] using s.property.2 l x
  have hd := congrArg (fun f : b5_V Λ F → ℂ ↦ fderiv ℂ f z v) he
  simp only [Function.comp_def, id_eq, Pi.mul_def] at hl hr
  rw [hl.fderiv, hr.fderiv] at hd
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, b52_thetaExponent_apply, smul_eq_mul,
    neg_mul, neg_neg, mul_add, mul_assoc, mul_comm, mul_left_comm] using hd

theorem b52_no_affine_logarithmic_derivative
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (v : b5_V Λ F) (hv : v ≠ 0) (L : b5_V Λ F →ₗ[ℂ] ℂ) (c : ℂ) :
    ¬ ∀ z, fderiv ℂ s.val z v = (L z + c) * s.val z := by
  intro hD
  obtain ⟨z, hz⟩ : ∃ z, s.val z ≠ 0 := by
    by_contra hn
    exact hs (funext fun z ↦ by simpa using not_not.mp (not_exists.mp hn z))
  have hL : ∀ l, L (b5_lattice Λ F l) =
      (Real.pi : ℂ) * b5_H Λ F hF Q (b5_lattice Λ F l) v := by
    intro l
    have hj : b5_factor Λ F hF Q l z ≠ 0 :=
      mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
    have hd := b52_section_fderiv_translate Λ F hF Q s l z v
    rw [hD, hD, s.property.2 l z, pow_one, map_add] at hd
    have he : (L (b5_lattice Λ F l) -
        (Real.pi : ℂ) * b5_H Λ F hF Q (b5_lattice Λ F l) v) *
        b5_factor Λ F hF Q l z * s.val z = 0 := by
      linear_combination hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hz)).resolve_right hj)
  let L' : b5_V Λ F →ₗ[ℂ] ℂ := (Real.pi : ℂ)⁻¹ • L
  obtain ⟨l, hl⟩ := b52_H_not_linear_on_lattice Λ F hF Q hpos v hv L'
  apply hl
  change (Real.pi : ℂ)⁻¹ * L (b5_lattice Λ F l) = _
  rw [hL, ← mul_assoc, inv_mul_cancel₀ (show (Real.pi : ℂ) ≠ 0 by
    exact_mod_cast Real.pi_ne_zero), one_mul]

end HodgeLean.Foundations.Program
