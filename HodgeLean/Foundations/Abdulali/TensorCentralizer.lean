import HodgeLean.Foundations.Abdulali.SkewCentralizer

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali

private def tensorCoordinates (U : Type*) [AddCommGroup U] [Module ℂ U] :
    ((Fin 2 → ℂ) ⊗[ℂ] U) ≃ₗ[ℂ] (Fin 2 → U) :=
  TensorProduct.comm ℂ _ _ ≪≫ₗ TensorProduct.piScalarRight ℂ ℂ U (Fin 2)

private lemma tensorCoordinates_tmul {U : Type*} [AddCommGroup U] [Module ℂ U]
    (x : Fin 2 → ℂ) (u : U) : tensorCoordinates U (x ⊗ₜ[ℂ] u) = fun i => x i • u := by
  ext i
  simp [tensorCoordinates, TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
    TensorProduct.piScalarRightHomBil]

private lemma tensorCoordinates_action {U : Type*} [AddCommGroup U] [Module ℂ U]
    (m : Matrix (Fin 2) (Fin 2) ℂ) (z : (Fin 2 → ℂ) ⊗[ℂ] U) :
    tensorCoordinates U ((Matrix.toLin' m).rTensor U z) =
      twoCopyAction m (tensorCoordinates U z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    ext i
    simp [LinearMap.rTensor_tmul, Matrix.toLin'_apply, tensorCoordinates_tmul,
      twoCopyAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_smul, smul_smul]
  | add z w hz hw =>
    simp only [map_add, hz, hw]
    ext i
    simp [twoCopyAction, smul_add, Finset.sum_add_distrib]

private lemma tensorCoordinates_form {U : Type*} [AddCommGroup U] [Module ℂ U]
    (E : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) ⊗[ℂ] U))
    (B : LinearMap.BilinForm ℂ U)
    (h : ∀ (x y : Fin 2 → ℂ) (u v : U),
      E (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) = (x 0 * y 1 - x 1 * y 0) * B u v)
    (z w : (Fin 2 → ℂ) ⊗[ℂ] U) :
    E z w = multiplicityAlternatingForm B (tensorCoordinates U z) (tensorCoordinates U w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      rw [h]
      simp only [tensorCoordinates_tmul, multiplicityAlternatingForm,
        LinearMap.sub_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply,
        map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    | add w w' hw hw' => simp only [map_add, hw, hw', LinearMap.add_apply]
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.add_apply]

/-- The matrix centralizer calculation in the actual tensor model supplied by
the matrix-module decomposition. The symmetric nondegenerate form and the
unique orthogonal multiplicity operator are obtained from the retained
polarization adjoint equation.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4, p. 923. -/
theorem polarized_tensor_centralizer (n : ℕ)
    (E : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)))
    (halt : ∀ z, E z z = 0) (hnd : E.Nondegenerate)
    (hadj : ∀ (m : Matrix (Fin 2) (Fin 2) ℂ)
      (z w : (Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)),
      E ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) w =
        E z ((Matrix.toLin' m.adjugate).rTensor (Fin n → ℂ) w)) :
    ∃ B : LinearMap.BilinForm ℂ (Fin n → ℂ),
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin n → ℂ),
        E (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)),
        ((∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
            X ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) =
              (Matrix.toLin' m).rTensor (Fin n → ℂ) (X z)) ∧
          ∀ z w, E (X z) w + E z (X w) = 0) ↔
        ∃! T : Module.End ℂ (Fin n → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          X = T.lTensor (Fin 2 → ℂ) := by
  obtain ⟨B, hsym, hB, hform⟩ := polarized_multiplicity_aux n E halt hnd hadj
  refine ⟨B, hsym, hB, hform, ?_⟩
  intro X
  let q := tensorCoordinates (Fin n → ℂ)
  let Y := q.conj X
  have hY (z) : Y (q z) = q (X z) := by simp [Y]
  have hEq (T : Module.End ℂ (Fin n → ℂ)) :
      (∀ z i, Y z i = T (z i)) ↔ X = T.lTensor (Fin 2 → ℂ) := by
    constructor
    · intro h
      apply LinearMap.ext
      intro z
      apply q.injective
      induction z using TensorProduct.inductionOn with
      | tmul x u =>
        ext i
        rw [← hY]
        simp only [q, tensorCoordinates_tmul, h, map_smul, LinearMap.lTensor_tmul]
      | add z w hz hw => simp only [map_add, hz, hw]
    · intro h z i
      obtain ⟨w, rfl⟩ := q.surjective z
      rw [hY, h]
      induction w using TensorProduct.inductionOn with
      | tmul x u => simp [q, LinearMap.lTensor_tmul, tensorCoordinates_tmul]
      | add z w hz hw => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hz hw
  have hConditions :
      ((∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
          X ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) =
            (Matrix.toLin' m).rTensor (Fin n → ℂ) (X z)) ∧
        ∀ z w, E (X z) w + E z (X w) = 0) ↔
      ((∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
          Y (twoCopyAction m z) = twoCopyAction m (Y z)) ∧
        ∀ z w, multiplicityAlternatingForm B (Y z) w +
          multiplicityAlternatingForm B z (Y w) = 0) := by
    constructor
    · rintro ⟨hc, hs⟩
      constructor
      · intro m z
        obtain ⟨w, rfl⟩ := q.surjective z
        rw [← tensorCoordinates_action, hY, hc, tensorCoordinates_action, hY]
      · intro z w
        obtain ⟨z, rfl⟩ := q.surjective z
        obtain ⟨w, rfl⟩ := q.surjective w
        rw [hY, hY]
        simpa only [tensorCoordinates_form E B hform] using hs z w
    · rintro ⟨hc, hs⟩
      constructor
      · intro m z
        apply q.injective
        rw [tensorCoordinates_action, ← hY, ← hY, tensorCoordinates_action]
        exact hc m (q z)
      · intro z w
        have hh := hs (q z) (q w)
        rw [hY, hY] at hh
        simpa only [tensorCoordinates_form E B hform] using hh
  rw [hConditions, split_skew_centralizer_normal_form]
  constructor
  · rintro ⟨T, ⟨hsk, hT⟩, hu⟩
    exact ⟨T, ⟨hsk, (hEq T).mp hT⟩, fun S hS => hu S ⟨hS.1, (hEq S).mpr hS.2⟩⟩
  · rintro ⟨T, ⟨hsk, hT⟩, hu⟩
    exact ⟨T, ⟨hsk, (hEq T).mpr hT⟩, fun S hS => hu S ⟨hS.1, (hEq S).mp hS.2⟩⟩

end HodgeLean.Foundations.Abdulali
