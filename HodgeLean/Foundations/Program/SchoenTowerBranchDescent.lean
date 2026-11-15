import HodgeLean.Foundations.Program.SchoenTowerBranchDescentProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The insertion square determines a unique map from the specified symmetric quotient.
Source: SGA 1, Exposé V, §1, categorical quotient universal property. -/
theorem s2t_branch_descent (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃! a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ :=
  s2t_branch_descent_aux C P B h b π γ hπquot hγinv

example (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃! a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ :=
  s2t_branch_descent C P B h b π γ hπquot hγinv

end HodgeLean.Foundations.Program
