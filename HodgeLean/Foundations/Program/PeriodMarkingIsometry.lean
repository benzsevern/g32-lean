import HodgeLean.Foundations.Program.PeriodMarkingDefs

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program

theorem b64b_marking_of_hermitian_isometry
    (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ M) (R : LinearMap.BilinForm ℤ N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (hA : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (hB : B.baseChange ℚ ∘ₗ B.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (sA : ∀ x y, Q.baseChange ℚ (A.baseChange ℚ x) y =
      -Q.baseChange ℚ x (A.baseChange ℚ y))
    (sB : ∀ x y, R.baseChange ℚ (B.baseChange ℚ x) y =
      -R.baseChange ℚ x (B.baseChange ℚ y))
    (e : WithJ (ℚ ⊗[ℤ] M) ⟨A.baseChange ℚ, hA⟩ ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      WithJ (ℚ ⊗[ℤ] N) ⟨B.baseChange ℚ, hB⟩)
    (he : ∀ x y, b64b_latticeH N R ⟨B.baseChange ℚ, hB⟩ sB (e x) (e y) =
      b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA x y) :
    ∃ m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] N),
      (∀ x, m (A.baseChange ℚ x) = B.baseChange ℚ (m x)) ∧
      ∀ x y, R.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y := by
  let jA := (⟨A.baseChange ℚ, hA⟩ :
    {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
  let jB := (⟨B.baseChange ℚ, hB⟩ :
    {J : Module.End ℚ (ℚ ⊗[ℤ] N) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
  let m := (WithJ.equiv jA).symm.trans
    ((e.restrictScalars ℚ).trans (WithJ.equiv jB))
  refine ⟨m, ?_, ?_⟩
  · intro x
    have hx : (WithJ.equiv jA).symm (A.baseChange ℚ x) =
        (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) •
          ((WithJ.equiv jA).symm x) := by
      apply (WithJ.equiv jA).injective
      rw [LinearEquiv.apply_symm_apply, equiv_omega_smul, LinearEquiv.apply_symm_apply]
    change (WithJ.equiv jB) (e ((WithJ.equiv jA).symm (A.baseChange ℚ x))) =
      B.baseChange ℚ ((WithJ.equiv jB) (e ((WithJ.equiv jA).symm x)))
    rw [hx, map_smul, equiv_omega_smul]
  · intro x y
    exact congrArg QuadraticAlgebra.im
      (he ((WithJ.equiv jA).symm x) ((WithJ.equiv jA).symm y))

end HodgeLean.Foundations.Program
