import HodgeLean.Foundations.Program.TorusAlgebraizationB52Characters

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_seedForPoint (z : b5_V Λ F) : b5_V Λ F →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w ↦ (Real.pi : ℂ) * b5_H Λ F hF Q z w
      map_add' := by
        intro x y
        rw [b5_H_add_right]
        ring
      map_smul' := by
        intro a w
        simp only [b52_H_smul_right, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp] theorem b52_seedForPoint_apply (z w : b5_V Λ F) :
    b52_seedForPoint Λ F hF Q z w = (Real.pi : ℂ) * b5_H Λ F hF Q z w := rfl

theorem b52_factor_zero (z : b5_V Λ F) : b5_factor Λ F hF Q 0 z = 1 := by
  simp [b5_factor, b5_chi, b5_refinement, b5_H]

#print axioms b52_factor_zero

theorem b52_seed_diagonal_eq
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (z : b5_V Λ F) :
    (b52_exponentialSeedSection Λ F hF Q hpos hcocycle
      (b52_seedForPoint Λ F hF Q z)).val z =
      Complex.exp ((Real.pi : ℂ) * b5_H Λ F hF Q z z) *
        ∑' l : Λ, (b5_factor Λ F hF Q l 0)⁻¹ * (b52_coverCharacter Λ F hF Q l z : ℂ) := by
  change b52_periodize (b5_lattice Λ F).toAddMonoidHom (b5_factor Λ F hF Q)
    (fun w ↦ Complex.exp (b52_seedForPoint Λ F hF Q z w)) z = _
  rw [b52_periodize_exponential_eq]
  simp only [b52_seedForPoint_apply, b52_thetaExponent_apply]
  congr 1
  apply tsum_congr
  intro l
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  unfold b52_coverCharacter
  rw [Circle.coe_exp]
  congr 1
  rw [← hherm z (b5_lattice Λ F l)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

#print axioms b52_seed_diagonal_eq

theorem b52_exists_nonzero_section
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ))
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z) :
    ∃ s : b5_sections Λ F hF Q 1, s.val ≠ 0 := by
  have hc0 : (b5_factor Λ F hF Q 0 0)⁻¹ ≠ 0 := by
    rw [b52_factor_zero]
    norm_num
  obtain ⟨x, hx⟩ := b52_torus_character_series_nonzero Λ F hF Q himag hpos
    (fun l ↦ (b5_factor Λ F hF Q l 0)⁻¹)
    (b52_summable_norm_inv_factor Λ F hF Q hpos 0) hc0
  obtain ⟨w, rfl⟩ := Quotient.exists_rep x
  change (∑' l : Λ, (b5_factor Λ F hF Q l 0)⁻¹ *
    (b52_coverCharacter Λ F hF Q l (b2_coord _ w) : ℂ)) ≠ 0 at hx
  refine ⟨b52_exponentialSeedSection Λ F hF Q hpos hcocycle
    (b52_seedForPoint Λ F hF Q (b2_coord _ w)), ?_⟩
  intro hs
  have he := congrFun hs (b2_coord _ w)
  rw [b52_seed_diagonal_eq Λ F hF Q hherm hpos hcocycle] at he
  exact (mul_ne_zero (Complex.exp_ne_zero _) hx) he

#print axioms b52_exists_nonzero_section

end HodgeLean.Foundations.Program
