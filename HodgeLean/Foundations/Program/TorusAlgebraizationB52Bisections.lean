import HodgeLean.Foundations.Program.TorusAlgebraizationB52MultiplicationDual

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b52_function_bisection_finite_products
    {K X Y : Type*} [Field K]
    (U : Submodule K (X → K)) (V : Submodule K (Y → K)) [Module.Finite K U]
    (f : X → Y → K) (hx : ∀ y, (fun x ↦ f x y) ∈ U) (hy : ∀ x, f x ∈ V) :
    ∃ n : ℕ, ∃ u : Fin n → U, ∃ v : Fin n → V,
      ∀ x y, f x y = ∑ i, (u i).val x * (v i).val y := by
  classical
  let b := Module.finBasis K U
  let slice (y : Y) : U := ⟨fun x ↦ f x y, hx y⟩
  have hmem (i : Fin (Module.finrank K U)) :
      (fun y ↦ b.repr (slice y) i) ∈ V := by
    obtain ⟨c, hc⟩ := b52_dual_function_space_finite_evaluations U (b.coord i)
    have heq : (fun y ↦ b.repr (slice y) i) =
        ∑ x ∈ c.support, c x • f x := by
      funext y
      simpa [Finsupp.sum, slice] using hc (slice y)
    rw [heq]
    exact V.sum_mem fun x _ ↦ V.smul_mem (c x) (hy x)
  let v (i : Fin (Module.finrank K U)) : V := ⟨_, hmem i⟩
  refine ⟨Module.finrank K U, b, v, ?_⟩
  intro x y
  have h := congrArg (fun u : U ↦ u.val x) (b.sum_repr (slice y))
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_bisection_diagonal_mem_multiplication_range (i j : ℕ)
    [Module.Finite ℂ (b5_sections Λ F hF Q (3 * i))]
    (f : b5_V Λ F → b5_V Λ F → ℂ)
    (hx : ∀ w, (fun z ↦ f z w) ∈ b5_sections Λ F hF Q (3 * i))
    (hy : ∀ z, f z ∈ b5_sections Λ F hF Q (3 * j))
    (s : b5_sections Λ F hF Q (3 * (i + j))) (hs : ∀ z, s.val z = f z z) :
    s ∈ LinearMap.range (b52_sectionMultiplication Λ F hF Q i j) := by
  classical
  obtain ⟨n, u, v, huv⟩ := b52_function_bisection_finite_products
    (b5_sections Λ F hF Q (3 * i)) (b5_sections Λ F hF Q (3 * j)) f hx hy
  refine ⟨∑ a : Fin n, u a ⊗ₜ[ℂ] v a, ?_⟩
  apply Subtype.ext
  funext z
  simpa [b52_sectionMultiplication] using (huv z z).symm.trans (hs z).symm

end HodgeLean.Foundations.Program
