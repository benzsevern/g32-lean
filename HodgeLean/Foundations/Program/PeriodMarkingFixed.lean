import HodgeLean.Foundations.Program.PeriodMarkingIsometry
import HodgeLean.Foundations.Program.PeriodMarkingLattice

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

def b64b_fixedCoordinates : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ]
    (Fin 6 → QuadraticAlgebra ℚ (-3) 0) :=
  ((Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ).equivFun.trans
    { toFun := fun x i => ⟨x (i, 0), x (i, 1)⟩
      invFun := fun x p => if p.2 = 0 then (x p.1).re else (x p.1).im
      left_inv := by
        intro x
        funext ⟨i, j⟩
        fin_cases j <;> rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro q x; rfl }

theorem b64b_fixedCoordinates_tmul (q : ℚ) (x : b60_Lattice) (i : Fin 6) :
    b64b_fixedCoordinates (q ⊗ₜ[ℤ] x) i =
      ⟨q * x (i, 0), q * x (i, 1)⟩ := by
  change (⟨((Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ).repr
      (q ⊗ₜ[ℤ] x) (i, 0),
    ((Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ).repr
      (q ⊗ₜ[ℤ] x) (i, 1)⟩ : QuadraticAlgebra ℚ (-3) 0) = _
  simp only [Module.Basis.baseChange_repr_tmul, Pi.basisFun_repr,
    zsmul_eq_mul, mul_comm]

theorem b64b_fixedCoordinates_action (x : ℚ ⊗[ℤ] b60_Lattice) :
    b64b_fixedCoordinates (b60_omega.baseChange ℚ x) =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) • b64b_fixedCoordinates x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul q x =>
    ext i <;> simp [LinearMap.baseChange_tmul, b64b_fixedCoordinates_tmul,
      b60_omega, QuadraticAlgebra.omega_mul_mk]
    all_goals ring

theorem b64b_fixed_pairing (x y : ℚ ⊗[ℤ] b60_Lattice) :
    (b60_H (b64b_fixedCoordinates x) (b64b_fixedCoordinates y)).im =
      b60_E.baseChange ℚ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, QuadraticAlgebra.im_add, hx, hz]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, QuadraticAlgebra.im_add, hy, hz]
    | tmul r y =>
      simp only [b60_H, diagForm_apply,
        b64b_fixedCoordinates_tmul, LinearMap.BilinForm.baseChange_tmul]
      simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul,
        b60_E, b60_diag, Fin.sum_univ_succ, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
      ring

theorem b64b_marking_of_standard_isometry
    (M : Type*) [AddCommGroup M] (Q : LinearMap.BilinForm ℤ M)
    (A : M →ₗ[ℤ] M)
    (hA : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (sA : ∀ x y, Q.baseChange ℚ (A.baseChange ℚ x) y =
      -Q.baseChange ℚ x (A.baseChange ℚ y))
    (e : WithJ (ℚ ⊗[ℤ] M) ⟨A.baseChange ℚ, hA⟩ ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (Fin 6 → QuadraticAlgebra ℚ (-3) 0))
    (he : ∀ x y, b60_H (e x) (e y) =
      b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA x y) :
    ∃ m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x)) ∧
      ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y := by
  let J := (⟨A.baseChange ℚ, hA⟩ :
    {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
  let m := (WithJ.equiv J).symm.trans
    ((e.restrictScalars ℚ).trans b64b_fixedCoordinates.symm)
  have hm (x : ℚ ⊗[ℤ] M) :
      b64b_fixedCoordinates (m x) = e ((WithJ.equiv J).symm x) :=
    b64b_fixedCoordinates.apply_symm_apply _
  refine ⟨m, ?_, ?_⟩
  · intro x
    apply b64b_fixedCoordinates.injective
    rw [b64b_fixedCoordinates_action, hm, hm]
    have hx : (WithJ.equiv J).symm (A.baseChange ℚ x) =
        (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) •
          ((WithJ.equiv J).symm x) := by
      apply (WithJ.equiv J).injective
      rw [LinearEquiv.apply_symm_apply, equiv_omega_smul, LinearEquiv.apply_symm_apply]
    rw [hx, map_smul]
  · intro x y
    rw [← b64b_fixed_pairing, hm, hm]
    exact congrArg QuadraticAlgebra.im
      (he ((WithJ.equiv J).symm x) ((WithJ.equiv J).symm y))

end HodgeLean.Foundations.Program
