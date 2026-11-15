import HodgeLean.Foundations.Program.SchoenTowerBranchAffineProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual point-addition map between affine symmetric quotients is an immersion.
Source: Schoen (1988), printed p. 12, branch insertion; SGA 1, Exposé V, §1. -/
theorem s2t_branch_affine_immersion (C P B : Over (Spec ↧ℂ))
    [IsAffine P.left] [IsAffine B.left] (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left :=
  s2t_branch_affine_immersion_aux C P B n b π γ hπinv hπquot hγquot a ha

example (C P B : Over (Spec ↧ℂ))
    [IsAffine P.left] [IsAffine B.left] (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left :=
  s2t_branch_affine_immersion C P B n b π γ hπinv hπquot hγquot a ha

#print axioms s2t_branch_affine_immersion
end HodgeLean.Foundations.Program
