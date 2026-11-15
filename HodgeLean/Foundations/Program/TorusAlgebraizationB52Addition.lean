import HodgeLean.Foundations.Program.TorusAlgebraizationB52Bisections
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Theta

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_factor_neg_neg (l : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q (-l) (-z) = b5_factor Λ F hF Q l z := by
  simp [b5_factor, b5_chi, b5_refinement, b5_H]

def b52_reflectedSection (k : ℕ) (s : b5_sections Λ F hF Q k) :
    b5_sections Λ F hF Q k := by
  refine ⟨fun z ↦ s.val (-z), s.property.1.comp differentiable_id.neg, ?_⟩
  intro l z
  change s.val (-(z + b5_lattice Λ F l)) =
    b5_factor Λ F hF Q l z ^ k * s.val (-z)
  rw [show -(z + b5_lattice Λ F l) = -z + b5_lattice Λ F (-l) by simp [add_comm],
    s.property.2, b52_factor_neg_neg]

theorem b52_factor_balanced_pair (l : Λ) (z a : b5_V Λ F) :
    b5_factor Λ F hF Q l (z + a) * b5_factor Λ F hF Q l (z - a) =
      b5_factor Λ F hF Q l z ^ 2 := by
  rw [sub_eq_add_neg, b5_factor_add_right, b5_factor_add_right]
  have he : Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a) *
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) (-a)) = 1 := by
    rw [← Complex.exp_add, ← mul_add, ← b5_H_add_right, add_neg_cancel]
    simp [b5_H]
  calc
    _ = b5_factor Λ F hF Q l z ^ 2 *
        (Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a) *
          Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) (-a))) := by ring
    _ = _ := by rw [he, mul_one]

def b52_balancedPairSection (k : ℕ) (s t : b5_sections Λ F hF Q k)
    (a : b5_V Λ F) : b5_sections Λ F hF Q (2 * k) := by
  refine ⟨fun z ↦ s.val (z + a) * t.val (z - a), ?_, ?_⟩
  · exact (s.property.1.comp (differentiable_id.add (differentiable_const a))).mul
      (t.property.1.comp (differentiable_id.sub (differentiable_const a)))
  · intro l z
    change s.val (z + b5_lattice Λ F l + a) * t.val (z + b5_lattice Λ F l - a) =
      b5_factor Λ F hF Q l z ^ (2 * k) * (s.val (z + a) * t.val (z - a))
    rw [add_right_comm z (b5_lattice Λ F l) a,
      show z + b5_lattice Λ F l - a = (z - a) + b5_lattice Λ F l by abel,
      s.property.2, t.property.2]
    calc
      _ = (b5_factor Λ F hF Q l (z + a) * b5_factor Λ F hF Q l (z - a)) ^ k *
          (s.val (z + a) * t.val (z - a)) := by rw [mul_pow]; ring
      _ = _ := by rw [b52_factor_balanced_pair, pow_mul]

theorem b52_theta_sum_difference_addition (k : ℕ)
    [Module.Finite ℂ (b5_sections Λ F hF Q (2 * k))]
    (s t : b5_sections Λ F hF Q k) :
    ∃ n : ℕ, ∃ u v : Fin n → b5_sections Λ F hF Q (2 * k),
      ∀ z w, s.val (z + w) * t.val (z - w) = ∑ i, (u i).val z * (v i).val w := by
  apply b52_function_bisection_finite_products
    (b5_sections Λ F hF Q (2 * k)) (b5_sections Λ F hF Q (2 * k))
  · intro w
    exact (b52_balancedPairSection Λ F hF Q k s t w).property
  · intro z
    have hp := (b52_balancedPairSection Λ F hF Q k s
      (b52_reflectedSection Λ F hF Q k t) z).property
    change (fun w ↦ s.val (w + z) * t.val (-(w - z))) ∈
      b5_sections Λ F hF Q (2 * k) at hp
    simpa only [neg_sub, add_comm] using hp

end HodgeLean.Foundations.Program
