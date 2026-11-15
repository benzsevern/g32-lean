import HodgeLean.Foundations.Program.TorusAlgebraizationB52WeightedAddition
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Averaging

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_weightedDiagonalSection (k a b : ℕ)
    (u : b5_sections Λ F hF Q (k * (a * (a + b))))
    (v : b5_sections Λ F hF Q (k * (b * (a + b)))) :
    b5_sections Λ F hF Q (k * (a + b) ^ 2) := by
  refine ⟨u.val * v.val, ?_⟩
  have hp := SetLike.mul_mem_graded (A := fun n ↦ b5_sections Λ F hF Q (k * n))
    u.property v.property
  convert hp using 1 <;> congr 1 <;> ring

def b52_weightedMultiplication (k a b : ℕ) :
    b5_sections Λ F hF Q (k * (a * (a + b))) ⊗[ℂ]
      b5_sections Λ F hF Q (k * (b * (a + b))) →ₗ[ℂ]
        b5_sections Λ F hF Q (k * (a + b) ^ 2) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (b52_weightedDiagonalSection Λ F hF Q k a b)
    (by intros; ext z; simp [b52_weightedDiagonalSection, add_mul])
    (by intros; ext z; simp [b52_weightedDiagonalSection, mul_assoc])
    (by intros; ext z; simp [b52_weightedDiagonalSection, mul_add])
    (by intros; ext z; simp [b52_weightedDiagonalSection, mul_left_comm]))

def b52_powerSection (k p : ℕ) (s : b5_sections Λ F hF Q k) :
    b5_sections Λ F hF Q (k * p) :=
  ⟨s.val ^ p, s.property.1.pow p, by
    intro l z
    simp only [Pi.pow_apply, s.property.2, mul_pow, ← pow_mul]⟩

variable
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_section_finite_traced_products (k a b : ℕ) (hab : a + b ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q (k * (a * (a + b))))]
    (s : b5_sections Λ F hF Q k) (t : b5_sections Λ F hF Q (k * (a * b)))
    (ht : t.val 0 ≠ 0) :
    ∃ r : ℕ, ∃ u : Fin r → b5_sections Λ F hF Q (k * (a * (a + b))),
      ∃ v : Fin r → b5_sections Λ F hF Q (k * (b * (a + b))),
      s = ∑ i, b52_descentTrace Λ F hF Q hherm himag hcocycle k (a + b) hab
        (b52_weightedDiagonalSection Λ F hF Q k a b (u i) (v i)) := by
  obtain ⟨r, u, v, huv⟩ := b52_dilated_section_finite_products Λ F hF Q k a b s t ht
  refine ⟨r, u, v, ?_⟩
  have he : b52_dilatedSection Λ F hF Q k (a + b) s =
      ∑ i, b52_weightedDiagonalSection Λ F hF Q k a b (u i) (v i) := by
    apply Subtype.ext
    funext z
    simpa only [b52_dilatedSection, b52_weightedDiagonalSection,
      Submodule.coe_sum, Finset.sum_apply, Pi.mul_apply] using huv z
  have hh := congrArg (b52_descentTrace Λ F hF Q hherm himag hcocycle k (a + b) hab) he
  rw [b52_descentTrace_dilation, map_sum] at hh
  exact hh

theorem b52_traced_weightedMultiplication_surjective (k a b : ℕ) (hab : a + b ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q (k * (a * (a + b))))]
    (t : b5_sections Λ F hF Q (k * (a * b))) (ht : t.val 0 ≠ 0) :
    Function.Surjective
      ((b52_descentTrace Λ F hF Q hherm himag hcocycle k (a + b) hab).comp
        (b52_weightedMultiplication Λ F hF Q k a b)) := by
  intro s
  obtain ⟨r, u, v, hs⟩ :=
    b52_section_finite_traced_products Λ F hF Q hherm himag hcocycle k a b hab s t ht
  refine ⟨∑ i, u i ⊗ₜ[ℂ] v i, ?_⟩
  rw [LinearMap.comp_apply, map_sum, map_sum]
  exact hs.symm

theorem b52_cubic_traced_weightedMultiplication_surjective
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (r a b : ℕ) (hab : a + b ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q ((3 * r) * (a * (a + b))))] :
    Function.Surjective
      ((b52_descentTrace Λ F hF Q hherm himag hcocycle (3 * r) (a + b) hab).comp
        (b52_weightedMultiplication Λ F hF Q (3 * r) a b)) := by
  obtain ⟨s, hs⟩ := b52_exists_nonzero_section Λ F hF Q hherm himag hpos hcocycle
  obtain ⟨c, hc⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs 0
  let t : b5_sections Λ F hF Q ((3 * r) * (a * b)) :=
    ⟨(b52_powerSection Λ F hF Q 3 (r * (a * b)) c).val, by
      simpa only [Nat.mul_assoc] using
        (b52_powerSection Λ F hF Q 3 (r * (a * b)) c).property⟩
  apply b52_traced_weightedMultiplication_surjective Λ F hF Q hherm himag hcocycle
    (3 * r) a b hab t
  exact pow_ne_zero _ hc

end HodgeLean.Foundations.Program
