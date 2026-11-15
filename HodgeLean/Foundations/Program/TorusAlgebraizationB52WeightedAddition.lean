import HodgeLean.Foundations.Program.TorusAlgebraizationB52Isogeny
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Addition

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_factor_weighted_pair (a b : ℕ) (l : Λ) (z w : b5_V Λ F) :
    b5_factor Λ F hF Q (a • l) ((a : ℂ) • z + (b : ℂ) • w) *
        b5_factor Λ F hF Q l (z - w) ^ (a * b) =
      b5_factor Λ F hF Q l z ^ (a * (a + b)) := by
  rw [b52_factor_weighted_translation, sub_eq_add_neg, b5_factor_add_right, mul_pow]
  have hn : b5_H Λ F hF Q (b5_lattice Λ F l) (-w) =
      -b5_H Λ F hF Q (b5_lattice Λ F l) w := by simp [b5_H]
  have he :
      Complex.exp (((a * b : ℕ) : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) w) *
        Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) (-w)) ^ (a * b) = 1 := by
    rw [hn, ← Complex.exp_nat_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  calc
    _ = (b5_factor Λ F hF Q l z ^ (a ^ 2) * b5_factor Λ F hF Q l z ^ (a * b)) *
        (Complex.exp (((a * b : ℕ) : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) w) *
          Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) (-w)) ^ (a * b)) := by ring
    _ = _ := by
      rw [he, mul_one, ← pow_add]
      congr 1
      ring

def b52_weightedPairSection (k a b : ℕ) (s : b5_sections Λ F hF Q k)
    (t : b5_sections Λ F hF Q (k * (a * b))) (w : b5_V Λ F) :
    b5_sections Λ F hF Q (k * (a * (a + b))) := by
  refine ⟨fun z ↦ s.val ((a : ℂ) • z + (b : ℂ) • w) * t.val (z - w), ?_, ?_⟩
  · exact (s.property.1.comp ((differentiable_id.const_smul (a : ℂ)).add
      (differentiable_const ((b : ℂ) • w)))).mul
      (t.property.1.comp (differentiable_id.sub_const w))
  · intro l z
    change s.val ((a : ℂ) • (z + b5_lattice Λ F l) + (b : ℂ) • w) *
        t.val (z + b5_lattice Λ F l - w) =
      b5_factor Λ F hF Q l z ^ (k * (a * (a + b))) *
        (s.val ((a : ℂ) • z + (b : ℂ) • w) * t.val (z - w))
    have he : (a : ℂ) • (z + b5_lattice Λ F l) + (b : ℂ) • w =
        ((a : ℂ) • z + (b : ℂ) • w) + b5_lattice Λ F (a • l) := by
      simp only [smul_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [he, show z + b5_lattice Λ F l - w = (z - w) + b5_lattice Λ F l by abel,
      s.property.2, t.property.2]
    calc
      _ = (b5_factor Λ F hF Q (a • l) ((a : ℂ) • z + (b : ℂ) • w) *
            b5_factor Λ F hF Q l (z - w) ^ (a * b)) ^ k *
          (s.val ((a : ℂ) • z + (b : ℂ) • w) * t.val (z - w)) := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm]
        ring
      _ = _ := by
        rw [b52_factor_weighted_pair]
        simp only [← pow_mul, Nat.mul_comm]

theorem b52_theta_weighted_addition (k a b : ℕ)
    [Module.Finite ℂ (b5_sections Λ F hF Q (k * (a * (a + b))))]
    (s : b5_sections Λ F hF Q k) (t : b5_sections Λ F hF Q (k * (a * b))) :
    ∃ n : ℕ, ∃ u : Fin n → b5_sections Λ F hF Q (k * (a * (a + b))),
      ∃ v : Fin n → b5_sections Λ F hF Q (k * (b * (a + b))),
      ∀ z w, s.val ((a : ℂ) • z + (b : ℂ) • w) * t.val (z - w) =
        ∑ i, (u i).val z * (v i).val w := by
  apply b52_function_bisection_finite_products
    (b5_sections Λ F hF Q (k * (a * (a + b))))
    (b5_sections Λ F hF Q (k * (b * (a + b))))
  · intro w
    exact (b52_weightedPairSection Λ F hF Q k a b s t w).property
  · intro z
    let tr : b5_sections Λ F hF Q (k * (b * a)) :=
      b52_reflectedSection Λ F hF Q (k * (b * a))
        ⟨t.val, by simpa only [Nat.mul_comm b a] using t.property⟩
    have hp := (b52_weightedPairSection Λ F hF Q k b a s tr z).property
    change (fun w ↦ s.val ((b : ℂ) • w + (a : ℂ) • z) * t.val (-(w - z))) ∈
      b5_sections Λ F hF Q (k * (b * (b + a))) at hp
    simpa only [neg_sub, add_comm] using hp

theorem b52_dilated_section_finite_products (k a b : ℕ)
    [Module.Finite ℂ (b5_sections Λ F hF Q (k * (a * (a + b))))]
    (s : b5_sections Λ F hF Q k) (t : b5_sections Λ F hF Q (k * (a * b)))
    (ht : t.val 0 ≠ 0) :
    ∃ n : ℕ, ∃ u : Fin n → b5_sections Λ F hF Q (k * (a * (a + b))),
      ∃ v : Fin n → b5_sections Λ F hF Q (k * (b * (a + b))),
      ∀ z, s.val (((a + b : ℕ) : ℂ) • z) = ∑ i, (u i).val z * (v i).val z := by
  obtain ⟨n, u, v, huv⟩ := b52_theta_weighted_addition Λ F hF Q k a b s t
  refine ⟨n, u, fun i ↦ (t.val 0)⁻¹ • v i, ?_⟩
  intro z
  have hz := huv z z
  simp only [sub_self, ← add_smul, ← Nat.cast_add] at hz
  change s.val (((a + b : ℕ) : ℂ) • z) =
    ∑ i, (u i).val z * ((t.val 0)⁻¹ * (v i).val z)
  calc
    _ = (t.val 0)⁻¹ * (s.val (((a + b : ℕ) : ℂ) • z) * t.val 0) := by
      rw [mul_left_comm, inv_mul_cancel₀ ht, mul_one]
    _ = (t.val 0)⁻¹ * ∑ i, (u i).val z * (v i).val z := by rw [hz]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end HodgeLean.Foundations.Program
