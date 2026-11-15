import HodgeLean.Foundations.PositivePolarizationLinear

/-! # The model forms on `ℚ²` and `ℚ⁴`

Helper computations for `PositivePolarizationProofs.lean` (lane `p1l_`): a real functional on
`ℝ ⊗ ℚⁿ` is determined by its values on the `1 ⊗ eᵢ`, and the explicit models
`p1_modelForm`, `-p1_modelForm` and `p1_modelForm₄`.
-/

noncomputable section

open Module
open scoped TensorProduct
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations

section Pi

variable {n : ℕ}

/-- A real functional on `ℝ ⊗ ℚⁿ` at `1 ⊗ v` is `Σ vᵢ φ (1 ⊗ eᵢ)`. -/
theorem p1l_apply_pi (φ : Dual ℝ (ℝ ⊗[ℚ] (Fin n → ℚ))) (v : Fin n → ℚ) :
    φ (1 ⊗ₜ v) = ∑ i, (v i : ℝ) * φ (1 ⊗ₜ Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (v i) : Fin n → ℚ) = v i • Pi.single i 1 by
      ext j; by_cases h : j = i <;> simp [h],
    TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, Rat.smul_def]

/-- Real functionals on `ℝ ⊗ ℚⁿ` agreeing on the `1 ⊗ eᵢ` are equal. -/
theorem p1l_dual_ext_pi {φ ψ : Dual ℝ (ℝ ⊗[ℚ] (Fin n → ℚ))}
    (h : ∀ i, φ (1 ⊗ₜ Pi.single i 1) = ψ (1 ⊗ₜ Pi.single i 1)) : φ = ψ :=
  p1l_dual_ext fun v => by rw [p1l_apply_pi, p1l_apply_pi]; simp only [h]

end Pi

section Model2

theorem p1l_modelJ_e0 : p1_modelJ (Pi.single 0 1) = Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ, Matrix.mulVec, dotProduct]

theorem p1l_modelJ_e1 : p1_modelJ (Pi.single 1 1) = -Pi.single 0 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ, Matrix.mulVec, dotProduct]

/-- `B (φ ∘ J, ψ)` for `ω = ±(e₀ ∧ e₁)`, in coordinates. -/
theorem p1l_model_value (s : ℝ) (hs : s = 1 ∨ s = -1) (ω : ⋀[ℚ]^2 (Fin 2 → ℚ))
    (hω : ∀ φ, p1_realContract ω φ = s • p1_realContract p1_modelForm φ)
    (φ ψ : Dual ℝ (ℝ ⊗[ℚ] (Fin 2 → ℚ))) :
    ψ (p1_realContract ω (φ ∘ₗ p1_modelJ.baseChange ℝ)) =
      s * (φ (1 ⊗ₜ Pi.single 1 1) * ψ (1 ⊗ₜ Pi.single 1 1) +
        φ (1 ⊗ₜ Pi.single 0 1) * ψ (1 ⊗ₜ Pi.single 0 1)) := by
  rcases hs with rfl | rfl
  all_goals simp [hω, p1_modelForm, p1l_realContract_ιMulti, LinearMap.baseChange_tmul, p1l_modelJ_e0,
    p1l_modelJ_e1, TensorProduct.tmul_neg]
  all_goals ring

theorem p1l_proj_ne_zero {n : ℕ} (i : Fin n) : (LinearMap.proj i : Dual ℚ (Fin n → ℚ)) ≠ 0 :=
  fun h => by simpa using LinearMap.congr_fun h (Pi.single i 1)

/-- `e₀ ∧ e₁` is positive for `J`. -/
theorem p1l_isPositive_model : p1_IsPositive p1_modelForm (p1_modelJ.baseChange ℝ) := by
  have h1 : ∀ φ, p1_realContract p1_modelForm φ = (1 : ℝ) • p1_realContract p1_modelForm φ :=
    fun φ => (one_smul ℝ _).symm
  refine ⟨fun φ ψ => ?_, fun φ hφ => ?_⟩
  · rw [p1l_model_value 1 (Or.inl rfl) _ h1]
    simp [p1_modelForm, p1l_realContract_ιMulti, LinearMap.baseChange_tmul, p1l_modelJ_e0,
      p1l_modelJ_e1, TensorProduct.tmul_neg]
    ring
  · rw [p1l_model_value 1 (Or.inl rfl) _ h1, one_mul]
    by_contra hle
    apply hφ
    have h0 : φ (1 ⊗ₜ Pi.single 0 1) = 0 := by
      nlinarith [sq_nonneg (φ (1 ⊗ₜ Pi.single 0 1)), sq_nonneg (φ (1 ⊗ₜ Pi.single 1 1))]
    have h1 : φ (1 ⊗ₜ Pi.single 1 1) = 0 := by
      nlinarith [sq_nonneg (φ (1 ⊗ₜ Pi.single 0 1)), sq_nonneg (φ (1 ⊗ₜ Pi.single 1 1))]
    refine p1l_dual_ext_pi fun i => ?_
    fin_cases i <;> simp [h0, h1]

/-- `-(e₀ ∧ e₁)` is nondegenerate and not positive for `J`. -/
theorem p1l_not_isPositive_model_neg :
    IsNondegenerate (-p1_modelForm) ∧ ¬ p1_IsPositive (-p1_modelForm) (p1_modelJ.baseChange ℝ) := by
  have h : IsNondegenerate p1_modelForm := isNondegenerate_e₀e₁
  refine ⟨⟨fun a b hab => h.1 ?_, fun y => ?_⟩, fun hP => ?_⟩
  · simpa [map_neg] using hab
  · obtain ⟨x, hx⟩ := h.2 (-y)
    exact ⟨x, by simpa [map_neg] using congrArg Neg.neg hx⟩
  · have := hP.2 _ (p1l_e_one_tmul_ne_zero (p1l_proj_ne_zero 0))
    rw [p1l_model_value (-1) (Or.inr rfl) _
      (fun φ => by rw [p1l_realContract_neg, neg_one_smul]; rfl)] at this
    simp [p1l_e_tmul] at this
    linarith

end Model2

section Model4

theorem p1l_modelJ₄_e0 : p1_modelJ₄ (Pi.single 0 1) = Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ₄, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem p1l_modelJ₄_e1 : p1_modelJ₄ (Pi.single 1 1) = -Pi.single 0 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ₄, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem p1l_modelJ₄_e2 : p1_modelJ₄ (Pi.single 2 1) = Pi.single 3 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ₄, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem p1l_modelJ₄_e3 : p1_modelJ₄ (Pi.single 3 1) = -Pi.single 2 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ₄, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem p1l_modelSwap₄_e0 : p1_modelSwap₄ (Pi.single 0 1) = Pi.single 2 1 := by
  ext i; fin_cases i <;> simp [p1_modelSwap₄, LinearMap.funLeft]

theorem p1l_modelSwap₄_e1 : p1_modelSwap₄ (Pi.single 1 1) = Pi.single 3 1 := by
  ext i; fin_cases i <;> simp [p1_modelSwap₄, LinearMap.funLeft]

theorem p1l_modelSwap₄_e2 : p1_modelSwap₄ (Pi.single 2 1) = Pi.single 0 1 := by
  ext i; fin_cases i <;> simp [p1_modelSwap₄, LinearMap.funLeft]

theorem p1l_modelSwap₄_e3 : p1_modelSwap₄ (Pi.single 3 1) = Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [p1_modelSwap₄, LinearMap.funLeft]

theorem p1l_isNondegenerate_model₄ : IsNondegenerate p1_modelForm₄ := by
  have hsurj : Function.Surjective (contract p1_modelForm₄) := by
    intro x
    refine ⟨x 1 • LinearMap.proj 0 - x 0 • LinearMap.proj 1 - x 3 • LinearMap.proj 2 +
      x 2 • LinearMap.proj 3, ?_⟩
    ext i
    fin_cases i <;> simp [p1_modelForm₄]
  refine ⟨?_, hsurj⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank] at hsurj
  rw [Subspace.dual_finrank_eq]

theorem p1l_not_isPositive_model₄ :
    ¬ p1_IsPositive p1_modelForm₄ (p1_modelJ₄.baseChange ℝ) := by
  intro hP
  have := hP.2 _ (p1l_e_one_tmul_ne_zero (p1l_proj_ne_zero 2))
  simp [p1_modelForm₄, p1l_realContract_sub, p1l_realContract_ιMulti, LinearMap.baseChange_tmul,
    p1l_modelJ₄_e0, p1l_modelJ₄_e1, p1l_modelJ₄_e2, p1l_modelJ₄_e3, TensorProduct.tmul_neg,
    p1l_e_tmul] at this
  linarith

theorem p1l_modelSwap₄_comm : p1_modelSwap₄ ∘ₗ p1_modelJ₄ = p1_modelJ₄ ∘ₗ p1_modelSwap₄ := by
  refine (Pi.basisFun ℚ (Fin 4)).ext fun i => ?_
  fin_cases i <;> simp [p1l_modelJ₄_e0, p1l_modelJ₄_e1, p1l_modelJ₄_e2, p1l_modelJ₄_e3,
    p1l_modelSwap₄_e0, p1l_modelSwap₄_e1, p1l_modelSwap₄_e2, p1l_modelSwap₄_e3]

theorem p1l_modelSwap₄_ne_zero : p1_modelSwap₄ ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (Pi.single 0 1)) 2
  simp [p1l_modelSwap₄_e0] at this

theorem p1l_modelSwap₄_sq : p1_modelSwap₄ ∘ₗ p1_modelSwap₄ = LinearMap.id := by
  refine (Pi.basisFun ℚ (Fin 4)).ext fun i => ?_
  fin_cases i <;> simp [p1l_modelSwap₄_e0, p1l_modelSwap₄_e1, p1l_modelSwap₄_e2,
    p1l_modelSwap₄_e3]

theorem p1l_adjoint_modelSwap₄ (hω : IsNondegenerate p1_modelForm₄) :
    p1_adjoint p1_modelForm₄ hω p1_modelSwap₄ = -p1_modelSwap₄ := by
  refine p1l_adjoint_eq hω ?_
  ext φ i
  fin_cases i <;> simp [p1_modelForm₄, LinearMap.dualMap_apply, p1l_modelSwap₄_e0,
    p1l_modelSwap₄_e1, p1l_modelSwap₄_e2, p1l_modelSwap₄_e3]

theorem p1l_model₄ :
    ∃ hω : IsNondegenerate p1_modelForm₄,
      ¬ p1_IsPositive p1_modelForm₄ (p1_modelJ₄.baseChange ℝ) ∧
      p1_modelSwap₄ ∘ₗ p1_modelJ₄ = p1_modelJ₄ ∘ₗ p1_modelSwap₄ ∧ p1_modelSwap₄ ≠ 0 ∧
      LinearMap.trace ℚ (Fin 4 → ℚ) (p1_modelSwap₄ ∘ₗ p1_adjoint p1_modelForm₄ hω p1_modelSwap₄) =
        -4 := by
  refine ⟨p1l_isNondegenerate_model₄, p1l_not_isPositive_model₄, p1l_modelSwap₄_comm,
    p1l_modelSwap₄_ne_zero, ?_⟩
  rw [p1l_adjoint_modelSwap₄, LinearMap.comp_neg, p1l_modelSwap₄_sq, map_neg, LinearMap.trace_id,
    Module.finrank_fin_fun]
  norm_num

end Model4

end HodgeLean.Foundations
