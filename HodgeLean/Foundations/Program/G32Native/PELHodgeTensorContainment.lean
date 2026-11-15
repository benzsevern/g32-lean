import HodgeLean.Foundations.Program.G32Native.PELHodgeCircleForm

noncomputable section
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- Hodge orthogonality of a rational form and preservation of Hodge summands
by retained rational operators place the Hodge group in the connected
polarization-isometry centralizer.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem hodgeGroup_subset_pel_of_tensors
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Set (Module.End ℚ V))
    (hE : ∀ p q r s : ℤ, ∀ x ∈ H (p, q), ∀ y ∈ H (r, s),
      p - q + (r - s) ≠ 0 → E.baseChange ℂ x y = 0)
    (hR : ∀ T ∈ R, ∀ pq x, x ∈ H pq → T.baseChange ℂ x ∈ H pq) :
    g2_hodgeGroup H hH b ⊆
      pelGenericGroup ((LinearMap.toMatrix₂ b b E).map (algebraMap ℚ ℂ))
        ((fun T : Module.End ℚ V =>
          (LinearMap.toMatrix b b T).map (algebraMap ℚ ℂ)) '' R) := by
  let bc := Algebra.TensorProduct.basis ℂ b
  have hform : LinearMap.toMatrix₂ bc bc (E.baseChange ℂ) =
      (LinearMap.toMatrix₂ b b E).map (algebraMap ℚ ℂ) := by
    ext i j
    dsimp only [bc]
    simp only [LinearMap.toMatrix₂_apply, Algebra.TensorProduct.basis_apply,
      LinearMap.BilinForm.baseChange_tmul, one_mul, Matrix.map_apply, Algebra.smul_def, mul_one]
  have hi := hodgeGroup_subset_pelGenericGroup H hH b
    (LinearMap.toMatrix₂ b b E) ((LinearMap.toMatrix b b) '' R)
  have himage : (fun T => T.map (algebraMap ℚ ℂ)) ''
      ((LinearMap.toMatrix b b) '' R) =
      ((fun T : Module.End ℚ V =>
        (LinearMap.toMatrix b b T).map (algebraMap ℚ ℂ)) '' R) := by
    rw [Set.image_image]
  rw [himage] at hi
  apply hi
  rintro g ⟨z, hz⟩
  change (g : Matrix (Fin n) (Fin n) ℂ).transpose *
    ((LinearMap.toMatrix₂ b b E).map (algebraMap ℚ ℂ)) * g = _ ∧
    ∀ T ∈ ((fun T : Module.End ℚ V =>
      (LinearMap.toMatrix b b T).map (algebraMap ℚ ℂ)) '' R),
        (g : Matrix (Fin n) (Fin n) ℂ) * T = T * g
  constructor
  · have hm := congrArg (LinearMap.toMatrix₂ bc bc)
      (circleAction_preserves_form H hH (E.baseChange ℂ) hE z)
    rw [LinearMap.toMatrix₂_compl₁₂ bc bc bc bc, hform] at hm
    change (g : Matrix (Fin n) (Fin n) ℂ).transpose * _ * g = _
    rw [hz]
    exact hm
  · rintro _ ⟨T, hT, rfl⟩
    have hm := congrArg (LinearMap.toMatrix bc bc)
      (circleAction_commutes_of_preserves H hH (T.baseChange ℂ) (hR T hT) z)
    dsimp only [bc] at hm
    simp only [LinearMap.toMatrix_mul, LinearMap.toMatrix_baseChange] at hm
    rw [hz]
    exact hm

#print axioms hodgeGroup_subset_pel_of_tensors
end HodgeLean.Foundations.Program.GeneralTypeIII
