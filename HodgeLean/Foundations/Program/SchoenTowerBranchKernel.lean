import HodgeLean.Foundations.Program.SchoenTowerBranchKernelProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Insertion descends uniquely and preserves the specified branch scheme ideal.
Source: Schoen (1988), printed p. 12, the map defining the branch divisor;
SGA 1, Exposé V, §1, categorical quotient universal property. -/
theorem s2t_branch_descent_kernel (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃ a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ ∧
      a.left.ker = s2c_branchIdeal C B h γ b ∧
      ∀ a' : P ⟶ B, π ≫ a' = s2c_branchInsertion C h b ≫ γ → a' = a :=
  s2t_branch_descent_kernel_aux C P B h b π γ hπinv hπquot hγinv

example (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃ a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ ∧
      a.left.ker = s2c_branchIdeal C B h γ b ∧
      ∀ a' : P ⟶ B, π ≫ a' = s2c_branchInsertion C h b ≫ γ → a' = a :=
  s2t_branch_descent_kernel C P B h b π γ hπinv hπquot hγinv

end HodgeLean.Foundations.Program
