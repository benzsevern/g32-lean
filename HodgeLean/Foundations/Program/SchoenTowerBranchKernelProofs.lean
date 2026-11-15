import HodgeLean.Foundations.Program.SchoenTowerBranchDescent
import HodgeLean.Foundations.Program.SchoenTowerQuotientKernel

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The descended insertion retains exactly the branch scheme ideal.
Source: Schoen (1988), printed p. 12, the map defining the branch divisor;
SGA 1, Exposé V, §1, categorical quotient universal property. -/
theorem s2t_branch_descent_kernel_aux (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃ a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ ∧
      a.left.ker = s2c_branchIdeal C B h γ b ∧
      ∀ a' : P ⟶ B, π ≫ a' = s2c_branchInsertion C h b ≫ γ → a' = a := by
  obtain ⟨a, ha, hu⟩ := s2t_branch_descent C P B h b π γ hπquot hγinv
  refine ⟨a, ha, ?_, hu⟩
  rw [s2c_branchIdeal, ← ha, Over.comp_left]
  exact (s2t_kernel_comp π.left a.left
    (s2t_quotient_kernel_aux C P h π hπinv hπquot)).symm

end HodgeLean.Foundations.Program
