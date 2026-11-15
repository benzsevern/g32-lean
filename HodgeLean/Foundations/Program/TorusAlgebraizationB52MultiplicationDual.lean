import HodgeLean.Foundations.Program.TorusAlgebraizationB52Generation
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b52_dual_function_space_finite_evaluations
    {K X : Type*} [Field K] (W : Submodule K (X → K)) [Module.Finite K W]
    (φ : Module.Dual K W) :
    ∃ c : X →₀ K, ∀ f : W, φ f = c.sum (fun x a ↦ a * f.val x) := by
  let ev : X → Module.Dual K W := fun x ↦ (LinearMap.proj x).comp W.subtype
  have hspan : Submodule.span K (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro f hf
    have hex : ∃ x, f.val x ≠ 0 := by
      by_contra! h
      apply hf
      exact Subtype.ext (funext h)
    obtain ⟨x, hx⟩ := hex
    exact ⟨ev x, ⟨x, rfl⟩, hx⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (show φ ∈ Submodule.span K (Set.range ev) by rw [hspan]; trivial)
  refine ⟨c, fun f ↦ ?_⟩
  rw [← hc]
  simp [Finsupp.sum, ev]

theorem b52_tensor_map_surjective_of_product_dual
    {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (m : U ⊗[K] V →ₗ[K] W)
    (h : ∀ φ : Module.Dual K W, (∀ u v, φ (m (u ⊗ₜ[K] v)) = 0) → φ = 0) :
    Function.Surjective m := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro φ hφ
  apply h φ
  intro u v
  exact LinearMap.congr_fun hφ (u ⊗ₜ[K] v)

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_multiplication_surjective_of_evaluation_relations (i j : ℕ)
    [Module.Finite ℂ (b5_sections Λ F hF Q (3 * (i + j)))]
    (hrel : ∀ c : b5_V Λ F →₀ ℂ,
      (∀ f : b5_sections Λ F hF Q (3 * i),
        ∀ g : b5_sections Λ F hF Q (3 * j),
        c.sum (fun x a ↦ a * (f.val x * g.val x)) = 0) →
      ∀ s : b5_sections Λ F hF Q (3 * (i + j)),
        c.sum (fun x a ↦ a * s.val x) = 0) :
    Function.Surjective (b52_sectionMultiplication Λ F hF Q i j) := by
  apply b52_tensor_map_surjective_of_product_dual
  intro φ hφ
  obtain ⟨c, hc⟩ := b52_dual_function_space_finite_evaluations _ φ
  have hprod : ∀ f : b5_sections Λ F hF Q (3 * i),
      ∀ g : b5_sections Λ F hF Q (3 * j),
      c.sum (fun x a ↦ a * (f.val x * g.val x)) = 0 := by
    intro f g
    simpa [hc, b52_sectionMultiplication] using hφ f g
  ext s
  exact (hc s).trans (hrel c hprod s)

end HodgeLean.Foundations.Program
