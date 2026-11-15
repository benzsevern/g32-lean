import HodgeLean.Foundations.Program.TorusAlgebraizationDefs
import Mathlib.Algebra.Algebra.Operations

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b52_adjoin_one_of_successive_products
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (G : ℕ → Submodule R A) (htotal : iSup G = ⊤)
    (hzero : G 0 ≤ (⊥ : Subalgebra R A).toSubmodule)
    (hmul : ∀ n, G (n + 1) ≤ G 1 * G n) :
    Algebra.adjoin R (G 1 : Set A) = ⊤ := by
  let B := Algebra.adjoin R (G 1 : Set A)
  have hpiece : ∀ n, G n ≤ B.toSubmodule := by
    intro n
    induction n with
    | zero => exact fun _ hx ↦ (show (⊥ : Subalgebra R A) ≤ B from bot_le) (hzero hx)
    | succ n ih =>
      apply (hmul n).trans
      exact Submodule.mul_le.mpr fun x hx y hy ↦
        B.mul_mem (Algebra.subset_adjoin hx) (ih hy)
  have hall : (⊤ : Submodule R A) ≤ B.toSubmodule := by
    rw [← htotal]
    exact iSup_le hpiece
  apply top_unique
  intro x _
  exact hall (Submodule.mem_top)

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_grade_zero_le_constants
    (hconst : ∀ f : b5_sections Λ F hF Q 0, ∀ z, f.val z = f.val 0) :
    b5_grade Λ F hF Q 0 ≤ (⊥ : Subalgebra ℂ (b5_S Λ F hF Q)).toSubmodule := by
  rintro x ⟨f, rfl⟩
  change DirectSum.of _ 0 f ∈ (⊥ : Subalgebra ℂ (b5_S Λ F hF Q))
  apply Algebra.mem_bot.mpr
  refine ⟨f.val 0, ?_⟩
  rw [DirectSum.algebraMap_apply]
  congr 1
  apply Subtype.ext
  funext z
  exact (hconst f z).symm

theorem b52_generated_one_of_grade_products
    (hconst : ∀ f : b5_sections Λ F hF Q 0, ∀ z, f.val z = f.val 0)
    (hmul : ∀ n, b5_grade Λ F hF Q (n + 1) ≤
      b5_grade Λ F hF Q 1 * b5_grade Λ F hF Q n) :
    Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤ := by
  apply b52_adjoin_one_of_successive_products _ _
    (b52_grade_zero_le_constants Λ F hF Q hconst) hmul
  exact DFinsupp.iSup_range_lsingle

def b52_sectionMultiplication (i j : ℕ) :
    b5_sections Λ F hF Q (3 * i) ⊗[ℂ] b5_sections Λ F hF Q (3 * j) →ₗ[ℂ]
      b5_sections Λ F hF Q (3 * (i + j)) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun f g ↦ ⟨f.val * g.val,
      SetLike.mul_mem_graded (A := fun n ↦ b5_sections Λ F hF Q (3 * n))
        f.property g.property⟩)
    (by intros; ext z; simp [add_mul])
    (by intros; ext z; simp [mul_assoc])
    (by intros; ext z; simp [mul_add])
    (by intros; ext z; simp [mul_left_comm]))

theorem b52_multiplication_image_mem (i j : ℕ)
    (t : b5_sections Λ F hF Q (3 * i) ⊗[ℂ] b5_sections Λ F hF Q (3 * j)) :
    DirectSum.of _ (i + j) (b52_sectionMultiplication Λ F hF Q i j t) ∈
      b5_grade Λ F hF Q i * b5_grade Λ F hF Q j := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    change DirectSum.of (fun n ↦ b5_sections Λ F hF Q (3 * n)) (i + j)
      ⟨f.val * g.val, _⟩ ∈ _
    have hm := Submodule.mul_mem_mul
      (show DirectSum.of _ i f ∈ b5_grade Λ F hF Q i from ⟨f, rfl⟩)
      (show DirectSum.of _ j g ∈ b5_grade Λ F hF Q j from ⟨g, rfl⟩)
    rw [DirectSum.of_mul_of] at hm
    exact hm
  | add x y hx hy =>
    simpa only [map_add] using Submodule.add_mem _ hx hy

theorem b52_generated_one_of_multiplication_surjective
    (hconst : ∀ f : b5_sections Λ F hF Q 0, ∀ z, f.val z = f.val 0)
    (hsurj : ∀ n, Function.Surjective (b52_sectionMultiplication Λ F hF Q 1 n)) :
    Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤ := by
  apply b52_generated_one_of_grade_products Λ F hF Q hconst
  intro n
  rw [Nat.add_comm n 1]
  rintro x ⟨f, rfl⟩
  obtain ⟨t, rfl⟩ := hsurj n f
  exact b52_multiplication_image_mem Λ F hF Q 1 n t

theorem b52_multiplication_zero_surjective (i : ℕ) :
    Function.Surjective (b52_sectionMultiplication Λ F hF Q i 0) := by
  intro f
  let e : b5_sections Λ F hF Q (3 * 0) :=
    ⟨1, SetLike.one_mem_graded (fun n ↦ b5_sections Λ F hF Q (3 * n))⟩
  refine ⟨f ⊗ₜ[ℂ] e, ?_⟩
  apply Subtype.ext
  funext z
  change f.val z * 1 = f.val z
  exact mul_one _

end HodgeLean.Foundations.Program
