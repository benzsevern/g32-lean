import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaAction

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_refinement_nsmul (n : ℕ) (l : Λ) :
    b5_refinement Λ Q (n • l) = (n : ℤ) ^ 2 * b5_refinement Λ Q l := by
  unfold b5_refinement
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  split_ifs <;> ring

theorem b52_chi_nsmul (n : ℕ) (l : Λ) :
    b5_chi Λ Q (n • l) = b5_chi Λ Q l ^ (n ^ 2) := by
  unfold b5_chi
  rw [b52_refinement_nsmul, ← Circle.exp_natCast_mul]
  congr 1
  push_cast
  ring

theorem b52_factor_dilation (n : ℕ) (l : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q (n • l) ((n : ℂ) • z) =
      b5_factor Λ F hF Q l z ^ (n ^ 2) := by
  unfold b5_factor
  rw [b52_chi_nsmul]
  simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, b52_H_smul_left,
    b52_H_smul_right, star_natCast, Circle.coe_pow, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

def b52_dilatedSection (k n : ℕ) (s : b5_sections Λ F hF Q k) :
    b5_sections Λ F hF Q (k * n ^ 2) := by
  refine ⟨fun z ↦ s.val ((n : ℂ) • z),
    s.property.1.comp (differentiable_id.const_smul (n : ℂ)), ?_⟩
  intro l z
  change s.val ((n : ℂ) • (z + b5_lattice Λ F l)) =
    b5_factor Λ F hF Q l z ^ (k * n ^ 2) * s.val ((n : ℂ) • z)
  rw [smul_add, show (n : ℂ) • b5_lattice Λ F l = b5_lattice Λ F (n • l) by
    simp only [map_nsmul, Nat.cast_smul_eq_nsmul],
    s.property.2, b52_factor_dilation]
  simp only [← pow_mul, Nat.mul_comm]

theorem b52_dilatedSection_injective (k n : ℕ) (hn : n ≠ 0) :
    Function.Injective (b52_dilatedSection Λ F hF Q k n) := by
  intro s t h
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply Subtype.ext
  funext z
  have hz := congrArg (fun u : b5_sections Λ F hF Q (k * n ^ 2) ↦
    u.val ((n : ℂ)⁻¹ • z)) h
  simpa [b52_dilatedSection, smul_smul, hn'] using hz

theorem b52_factor_weighted_translation (a b : ℕ) (l : Λ) (z w : b5_V Λ F) :
    b5_factor Λ F hF Q (a • l) ((a : ℂ) • z + (b : ℂ) • w) =
      b5_factor Λ F hF Q l z ^ (a ^ 2) *
        Complex.exp (((a * b : ℕ) : ℂ) * Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) w) := by
  rw [b5_factor_add_right, b52_factor_dilation]
  simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, b52_H_smul_left,
    b52_H_smul_right, star_natCast]
  congr 2
  push_cast
  ring

def b52_descendedSection (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2))
    (ht : ∀ l z, t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * t.val z) :
    b5_sections Λ F hF Q k := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun z ↦ t.val ((n : ℂ)⁻¹ • z),
    t.property.1.comp (differentiable_id.const_smul (n : ℂ)⁻¹), ?_⟩
  intro l z
  change t.val ((n : ℂ)⁻¹ • (z + b5_lattice Λ F l)) = _
  rw [smul_add, ht]
  simp only [smul_smul, mul_inv_cancel₀ hn', one_smul]

theorem b52_dilatedSection_fractional_automorphy (k n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q k) (l : Λ) (z : b5_V Λ F) :
    (b52_dilatedSection Λ F hF Q k n s).val
        (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k *
        (b52_dilatedSection Λ F hF Q k n s).val z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  change s.val ((n : ℂ) • (z + (n : ℂ)⁻¹ • b5_lattice Λ F l)) =
    b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * s.val ((n : ℂ) • z)
  simpa only [smul_add, smul_smul, mul_inv_cancel₀ hn', one_smul] using
    s.property.2 l ((n : ℂ) • z)

theorem b52_dilated_descendedSection (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2))
    (ht : ∀ l z, t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * t.val z) :
    b52_dilatedSection Λ F hF Q k n
      (b52_descendedSection Λ F hF Q k n hn t ht) = t := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply Subtype.ext
  funext z
  change t.val ((n : ℂ)⁻¹ • ((n : ℂ) • z)) = t.val z
  simp only [smul_smul, inv_mul_cancel₀ hn', one_smul]

theorem b52_mem_dilatedSection_range_iff (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    t ∈ Set.range (b52_dilatedSection Λ F hF Q k n) ↔
      ∀ l z, t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
        b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * t.val z := by
  constructor
  · rintro ⟨s, rfl⟩
    exact b52_dilatedSection_fractional_automorphy Λ F hF Q k n hn s
  · intro ht
    exact ⟨b52_descendedSection Λ F hF Q k n hn t ht,
      b52_dilated_descendedSection Λ F hF Q k n hn t ht⟩

theorem b52_fractional_translation_factor (k n : ℕ) (hn : n ≠ 0)
    (l : Λ) (z : b5_V Λ F) :
    Complex.exp (-(((k * n ^ 2 : ℕ) : ℂ) * Real.pi *
        b5_H Λ F hF Q ((n : ℂ)⁻¹ • b5_lattice Λ F l) z)) *
      b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k =
        b5_factor Λ F hF Q l 0 ^ k := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hz : b5_H Λ F hF Q (b5_lattice Λ F l) 0 = 0 := by simp [b5_H]
  simp only [b5_factor, b52_H_smul_left, b52_H_smul_right,
    mul_pow, ← Complex.exp_nat_mul, hz]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  have hs : star ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := by simp
  rw [hs]
  field_simp [hn']
  ring

theorem b52_fractional_automorphy_iff_eigen (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    (∀ l z, t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * t.val z) ↔
    ∀ l, b52_thetaTranslate Λ F hF Q (k * n ^ 2)
      ((n : ℂ)⁻¹ • b5_lattice Λ F l) t.val =
        b5_factor Λ F hF Q l 0 ^ k • t.val := by
  constructor
  · intro ht l
    funext z
    change Complex.exp (-(((k * n ^ 2 : ℕ) : ℂ) * Real.pi *
      b5_H Λ F hF Q ((n : ℂ)⁻¹ • b5_lattice Λ F l) z)) *
        t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      b5_factor Λ F hF Q l 0 ^ k * t.val z
    rw [ht, ← mul_assoc, b52_fractional_translation_factor Λ F hF Q k n hn]
  · intro ht l z
    have hz := congrFun (ht l) z
    apply mul_left_cancel₀ (Complex.exp_ne_zero
      (-(((k * n ^ 2 : ℕ) : ℂ) * Real.pi *
        b5_H Λ F hF Q ((n : ℂ)⁻¹ • b5_lattice Λ F l) z)))
    rw [← mul_assoc, b52_fractional_translation_factor Λ F hF Q k n hn]
    exact hz

theorem b52_mem_dilatedSection_range_iff_eigen (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    t ∈ Set.range (b52_dilatedSection Λ F hF Q k n) ↔
      ∀ l, b52_thetaTranslate Λ F hF Q (k * n ^ 2)
        ((n : ℂ)⁻¹ • b5_lattice Λ F l) t.val =
          b5_factor Λ F hF Q l 0 ^ k • t.val := by
  exact (b52_mem_dilatedSection_range_iff Λ F hF Q k n hn t).trans
    (b52_fractional_automorphy_iff_eigen Λ F hF Q k n hn t)

theorem b52_fractional_translation_integrality
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (k n : ℕ) (hn : n ≠ 0) (l m : Λ) :
    ((k * n ^ 2 : ℕ) : ℝ) *
      (b5_H Λ F hF Q (b5_lattice Λ F m)
        ((n : ℂ)⁻¹ • b5_lattice Λ F l)).im =
      ((k : ℤ) * (n : ℤ) * Q m l : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [b52_H_smul_right]
  simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero, zero_div,
    zero_mul, add_zero, himag]
  simp [Complex.normSq]
  field_simp

theorem b52_fractional_translation_preserves_sections
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (k n : ℕ) (hn : n ≠ 0) (l : Λ)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    b52_thetaTranslate Λ F hF Q (k * n ^ 2)
      ((n : ℂ)⁻¹ • b5_lattice Λ F l) t.val ∈
        b5_sections Λ F hF Q (k * n ^ 2) := by
  apply b52_thetaTranslate_preserves_sections Λ F hF Q hherm
  intro m
  refine ⟨(k : ℤ) * (n : ℤ) * Q m l, ?_⟩
  simpa only [Int.cast_mul, Int.cast_natCast] using
    b52_fractional_translation_integrality Λ F hF Q himag k n hn l m

end HodgeLean.Foundations.Program
