import HodgeLean.Foundations.Program.TorusAlgebraizationB52Twisted

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_thetaTranslate (k : ℕ) (d : b5_V Λ F) :
    (b5_V Λ F → ℂ) →ₗ[ℂ] (b5_V Λ F → ℂ) where
  toFun f z := Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * f (z + d)
  map_add' f g := by ext z; simp [mul_add]
  map_smul' a f := by ext z; simp [mul_left_comm]

theorem b52_thetaTranslate_preserves_sections
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (k : ℕ) (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (k : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (s : b5_sections Λ F hF Q k) :
    b52_thetaTranslate Λ F hF Q k d s.val ∈ b5_sections Λ F hF Q k := by
  have hg : Differentiable ℂ (fun z ↦
      Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z))) := by
    simpa only [b52_seedForPoint_apply, mul_assoc, Pi.neg_apply] using
      (((b52_seedForPoint Λ F hF Q d).differentiable.const_mul (k : ℂ)).neg.cexp)
  refine ⟨hg.mul (s.property.1.comp (differentiable_id.add_const d)), ?_⟩
  intro l z
  change Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (z + b5_lattice Λ F l))) *
    s.val (z + b5_lattice Λ F l + d) = _
  rw [add_right_comm z (b5_lattice Λ F l) d, s.property.2, b5_factor_add_right,
    mul_pow, b5_H_add_right, mul_add, neg_add, Complex.exp_add]
  have he : Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (b5_lattice Λ F l))) *
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) d) ^ k = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    have hi : ∃ n : ℤ,
        (b5_H Λ F hF Q (b5_lattice Λ F l) ((k : ℂ) • d)).im = n := by
      simpa [b52_H_smul_right, Complex.mul_im] using hd l
    convert (b52_exp_hermitian_commutator_eq_one_iff Λ F hF Q hherm
      (b5_lattice Λ F l) ((k : ℂ) • d)).mpr hi using 1
    congr 1
    simp only [b52_H_smul_right, b52_H_smul_left, star_natCast]
    ring
  change _ = b5_factor Λ F hF Q l z ^ k *
    (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * s.val (z + d))
  calc
    _ = b5_factor Λ F hF Q l z ^ k *
        (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (b5_lattice Λ F l))) *
          Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) d) ^ k) *
        (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * s.val (z + d)) := by ring
    _ = _ := by rw [he]; ring

theorem b52_thetaTranslate_comp (k : ℕ) (d e : b5_V Λ F) :
    (b52_thetaTranslate Λ F hF Q k d).comp (b52_thetaTranslate Λ F hF Q k e) =
      Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q e d)) •
        b52_thetaTranslate Λ F hF Q k (d + e) := by
  ext f z
  change Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z)) *
      (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q e (z + d))) * f (z + d + e)) =
    Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q e d)) *
      (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q (d + e) z)) * f (z + (d + e)))
  rw [b5_H_add_right, (b52_H_real_bilinear Λ F hF Q).add_left]
  simp only [mul_add, neg_add, Complex.exp_add, add_assoc]
  ring

theorem b52_thetaTranslate_commutator (k : ℕ) (d e : b5_V Λ F) :
    (b52_thetaTranslate Λ F hF Q k d).comp (b52_thetaTranslate Λ F hF Q k e) =
      Complex.exp ((k : ℂ) * Real.pi * (b5_H Λ F hF Q d e - b5_H Λ F hF Q e d)) •
        (b52_thetaTranslate Λ F hF Q k e).comp (b52_thetaTranslate Λ F hF Q k d) := by
  rw [b52_thetaTranslate_comp, b52_thetaTranslate_comp, smul_smul, ← Complex.exp_add,
    add_comm e d]
  congr 2
  ring

theorem b52_thetaTranslate_injective (k : ℕ) (d : b5_V Λ F) :
    Function.Injective (b52_thetaTranslate Λ F hF Q k d) := by
  intro f g h
  funext z
  have hz := congrFun h (z - d)
  change Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (z - d))) * f (z - d + d) =
    Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (z - d))) * g (z - d + d) at hz
  rw [sub_add_cancel] at hz
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hz

def b52_sectionTranslation
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (k : ℕ) (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (k : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n) :
    Module.End ℂ (b5_sections Λ F hF Q k) :=
  (b52_thetaTranslate Λ F hF Q k d).restrict
    (fun f hf ↦ b52_thetaTranslate_preserves_sections Λ F hF Q hherm k d hd ⟨f, hf⟩)

theorem b52_thetaTranslate_mul (i j : ℕ) (d : b5_V Λ F) (f g : b5_V Λ F → ℂ) :
    b52_thetaTranslate Λ F hF Q (i + j) d (f * g) =
      b52_thetaTranslate Λ F hF Q i d f * b52_thetaTranslate Λ F hF Q j d g := by
  funext z
  change Complex.exp (-(((i + j : ℕ) : ℂ) * Real.pi * b5_H Λ F hF Q d z)) *
      (f (z + d) * g (z + d)) =
    (Complex.exp (-((i : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * f (z + d)) *
      (Complex.exp (-((j : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * g (z + d))
  simp only [Nat.cast_add, add_mul, neg_add, Complex.exp_add]
  ring

theorem b52_thetaTranslate_lattice (k : ℕ) (s : b5_sections Λ F hF Q k) (l : Λ) :
    b52_thetaTranslate Λ F hF Q k (b5_lattice Λ F l) s.val =
      ((b5_chi Λ Q l : ℂ) ^ k * Complex.exp ((k : ℂ) * (Real.pi / 2) *
        b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))) • s.val := by
  funext z
  change Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z)) *
      s.val (z + b5_lattice Λ F l) =
    ((b5_chi Λ Q l : ℂ) ^ k * Complex.exp ((k : ℂ) * (Real.pi / 2) *
      b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))) * s.val z
  rw [s.property.2, b5_factor, mul_pow, ← Complex.exp_nat_mul]
  have he :
      Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z)) *
        Complex.exp ((k : ℂ) * (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z +
          (Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))) =
      Complex.exp ((k : ℂ) * (Real.pi / 2) *
        b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (b5_chi Λ Q l : ℂ) ^ k *
        (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z)) *
          Complex.exp ((k : ℂ) * (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z +
            (Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l)))) * s.val z := by
      ring
    _ = _ := by rw [he]

end HodgeLean.Foundations.Program
