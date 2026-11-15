import HodgeLean.Foundations.Abdulali.TensorCentralizer

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali

/-- A polarized unital matrix representation has an orthogonal multiplicity
normal form, retaining the action, the alternating form, and every skew
centralizer operator. No invariant-generation assertion is a premise.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4, p. 923,
the split quaternionic representation calculation. -/
theorem polarized_matrix_representation_normal_form
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ V)
    (E : LinearMap.BilinForm ℂ V) (halt : ∀ z, E z z = 0) (hnd : E.Nondegenerate)
    (hadj : ∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z w,
      E (ρ m z) w = E z (ρ m.adjugate w)) :
    ∃ (n : ℕ) (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] V)
      (B : LinearMap.BilinForm ℂ (Fin n → ℂ)),
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
        ρ m (e z) = e ((Matrix.toLin' m).rTensor (Fin n → ℂ) z)) ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin n → ℂ),
        E (e (x ⊗ₜ[ℂ] u)) (e (y ⊗ₜ[ℂ] v)) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ V,
        ((∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z, X (ρ m z) = ρ m (X z)) ∧
          ∀ z w, E (X z) w + E z (X w) = 0) ↔
        ∃! T : Module.End ℂ (Fin n → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
  obtain ⟨n, e, he⟩ := matrix_module_aux V ρ
  have he' (m : Matrix (Fin 2) (Fin 2) ℂ) (z) :
      ρ m (e z) = e ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x u => simpa only [LinearMap.rTensor_tmul, Matrix.toLin'_apply] using he m x u
    | add z w hz hw => simp only [map_add, hz, hw]
  let F := E.compl₁₂ e.toLinearMap e.toLinearMap
  have hF : F.Nondegenerate := by
    constructor
    · intro z hz
      apply e.injective
      rw [map_zero]
      apply hnd.1
      intro w
      obtain ⟨w, rfl⟩ := e.surjective w
      exact hz w
    · intro w hw
      apply e.injective
      rw [map_zero]
      apply hnd.2
      intro z
      obtain ⟨z, rfl⟩ := e.surjective z
      exact hw z
  have hFadj (m : Matrix (Fin 2) (Fin 2) ℂ) z w :
      F ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) w =
        F z ((Matrix.toLin' m.adjugate).rTensor (Fin n → ℂ) w) := by
    change E (e ((Matrix.toLin' m).rTensor (Fin n → ℂ) z)) (e w) =
      E (e z) (e ((Matrix.toLin' m.adjugate).rTensor (Fin n → ℂ) w))
    rw [← he', ← he', hadj]
  obtain ⟨B, hsym, hB, hform, hcentral⟩ := polarized_tensor_centralizer n F
    (fun z => halt (e z)) hF hFadj
  refine ⟨n, e, B, hsym, hB, he', hform, ?_⟩
  intro X
  rw [← hcentral (e.symm.conj X)]
  have hX (z) : e (e.symm.conj X z) = X (e z) := by simp
  constructor
  · rintro ⟨hc, hs⟩
    constructor
    · intro m z
      apply e.injective
      rw [hX, ← he', hc, ← hX, he']
    · intro z w
      change E (e (e.symm.conj X z)) (e w) + E (e z) (e (e.symm.conj X w)) = 0
      rw [hX, hX]
      exact hs (e z) (e w)
  · rintro ⟨hc, hs⟩
    constructor
    · intro m z
      obtain ⟨z, rfl⟩ := e.surjective z
      rw [he', ← hX, hc, ← he', hX]
    · intro z w
      obtain ⟨z, rfl⟩ := e.surjective z
      obtain ⟨w, rfl⟩ := e.surjective w
      simpa only [F, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hX] using hs z w

end HodgeLean.Foundations.Abdulali
