import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaAction
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Generation

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (i j : ℕ) (d : b5_V Λ F)
    (hi : ∀ l : Λ, ∃ n : ℤ, (3 * i : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (hj : ∀ l : Λ, ∃ n : ℤ, (3 * j : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (hij : ∀ l : Λ, ∃ n : ℤ,
      (3 * (i + j) : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)

theorem b52_multiplication_translation_equivariant :
    (b52_sectionTranslation Λ F hF Q hherm (3 * (i + j)) d (by exact_mod_cast hij)).comp
        (b52_sectionMultiplication Λ F hF Q i j) =
      (b52_sectionMultiplication Λ F hF Q i j).comp
        (TensorProduct.map
          (b52_sectionTranslation Λ F hF Q hherm (3 * i) d (by exact_mod_cast hi))
          (b52_sectionTranslation Λ F hF Q hherm (3 * j) d (by exact_mod_cast hj))) := by
  apply TensorProduct.ext'
  intro s t
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  apply Subtype.ext
  change b52_thetaTranslate Λ F hF Q (3 * (i + j)) d (s.val * t.val) =
    b52_thetaTranslate Λ F hF Q (3 * i) d s.val *
      b52_thetaTranslate Λ F hF Q (3 * j) d t.val
  simpa only [Nat.mul_add] using
    b52_thetaTranslate_mul Λ F hF Q (3 * i) (3 * j) d s.val t.val

include hi hj in
theorem b52_multiplication_range_translation_invariant :
    Set.MapsTo
      (b52_sectionTranslation Λ F hF Q hherm (3 * (i + j)) d (by exact_mod_cast hij))
      (LinearMap.range (b52_sectionMultiplication Λ F hF Q i j))
      (LinearMap.range (b52_sectionMultiplication Λ F hF Q i j)) := by
  rintro s ⟨t, rfl⟩
  refine ⟨TensorProduct.map
    (b52_sectionTranslation Λ F hF Q hherm (3 * i) d (by exact_mod_cast hi))
    (b52_sectionTranslation Λ F hF Q hherm (3 * j) d (by exact_mod_cast hj)) t, ?_⟩
  exact (LinearMap.congr_fun
    (b52_multiplication_translation_equivariant Λ F hF Q hherm i j d hi hj hij) t).symm

end HodgeLean.Foundations.Program
