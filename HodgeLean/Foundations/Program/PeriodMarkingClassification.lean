import HodgeLean.Foundations.Program.PeriodMarkingFixed
import HodgeLean.Foundations.HermitianClassC8

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem b64b_rank_six (M : Type*) [AddCommGroup M]
    (B : Module.Basis (Fin 12) ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id}) :
    Module.finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (ℚ ⊗[ℤ] M) J) = 6 := by
  let : Module.Free ℤ M := Module.Free.of_basis B
  let : Module.Finite ℤ M := Module.Finite.of_basis B
  have hQ : Module.finrank ℚ (ℚ ⊗[ℤ] M) = 12 :=
    (Module.finrank_eq_card_basis (B.baseChange ℚ)).trans (Fintype.card_fin 12)
  have hK := finrank_withJ J
  omega

theorem b64b_standard_isometry_of_invariants
    (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (B : Module.Basis (Fin 12) ℤ M)
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (hA : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (sA : ∀ x y, Q.baseChange ℚ (A.baseChange ℚ x) y =
      -Q.baseChange ℚ x (A.baseChange ℚ y))
    (hh : (b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA).IsSymm)
    (hn : (b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA).Nondegenerate)
    (hsig : hermSignature (b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA) = (3, 3))
    (hdet : detClass (b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA) hh hn =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))) :
    ∃ e : WithJ (ℚ ⊗[ℤ] M) ⟨A.baseChange ℚ, hA⟩ ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (e x) (e y) = b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA x y := by
  let : Module.Free ℤ M := Module.Free.of_basis B
  let : Module.Finite ℤ M := Module.Finite.of_basis B
  exact HermitianClass.hermClass_rank_six_standard _ _ hh hn
    (b64b_rank_six M B _) hsig hdet

end HodgeLean.Foundations.Program
