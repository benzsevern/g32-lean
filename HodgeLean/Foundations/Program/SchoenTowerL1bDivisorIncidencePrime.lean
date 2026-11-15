import HodgeLean.Foundations.Program.SchoenCycleBranchAffineImage
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A retained incidence ideal is prime on every affine open met by its insertion image. -/
theorem s2v_l1b_divisor_incidence_ideal_prime
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] (n : ℕ)
    [IsIntegral (g3_power Z n).left]
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (b : ComplexPoint Z) (U : B.left.affineOpens)
    [Nonempty ((s2c_branchInsertion Z n b ≫ γ).left ⁻¹ᵁ U.1)] :
    ((s2c_branchIdeal Z B n γ b).ideal U).IsPrime := by
  rw [s2e_branchIdeal_affine_kernel]
  exact RingHom.ker_isPrime _

/-- An incidence ideal on an affine open is the whole ring or a prime ideal. -/
theorem s2v_l1b_divisor_incidence_ideal_top_or_prime
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] (n : ℕ)
    [IsIntegral (g3_power Z n).left]
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (b : ComplexPoint Z) (U : B.left.affineOpens) :
    (s2c_branchIdeal Z B n γ b).ideal U = ⊤ ∨
      ((s2c_branchIdeal Z B n γ b).ideal U).IsPrime := by
  let f := s2c_branchInsertion Z n b ≫ γ
  by_cases hn : Nonempty (f.left ⁻¹ᵁ U.1)
  · letI := hn
    exact Or.inr (s2v_l1b_divisor_incidence_ideal_prime Z B n γ b U)
  · left
    have hO : f.left ⁻¹ᵁ U.1 = ⊥ := by
      apply bot_unique
      intro x hx
      exact hn ⟨⟨x, hx⟩⟩
    letI : Subsingleton Γ((g3_power Z n).left, f.left ⁻¹ᵁ U.1) := by
      rw [hO]
      infer_instance
    rw [s2e_branchIdeal_affine_kernel]
    apply (Ideal.eq_top_iff_one _).mpr
    exact Subsingleton.elim _ _

end HodgeLean.Foundations.Program
