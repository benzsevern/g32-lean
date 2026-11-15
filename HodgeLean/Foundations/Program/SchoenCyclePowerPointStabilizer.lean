import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

/-! # Stabilizer subgroups of actual power points -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The subgroup of coordinate permutations fixing a specified actual power point.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
def s2e_powerPointStabilizer (Z : Over (Spec ↧ℂ)) (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | Point.map (s2_permute Z n σ) x = x}
  one_mem' := by
    change Point.map (s2_permute Z n 1) x = x
    rw [s2e_step1_permute_one]
    rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change Point.map (s2_permute Z n (σ * τ)) x = x
    rw [s2e_step1_permute_mul]
    change Point.map (s2_permute Z n σ) (Point.map (s2_permute Z n τ) x) = x
    rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    have he := congrArg (Point.map (s2_permute Z n σ⁻¹)) hσ
    change Point.map (s2_permute Z n σ ≫ s2_permute Z n σ⁻¹) x =
      Point.map (s2_permute Z n σ⁻¹) x at he
    rw [← s2e_step1_permute_mul, inv_mul_cancel, s2e_step1_permute_one] at he
    exact he.symm

end HodgeLean.Foundations.Program
