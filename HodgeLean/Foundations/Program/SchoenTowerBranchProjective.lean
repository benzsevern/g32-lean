import HodgeLean.Foundations.Program.SchoenTowerBranchProjectiveProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Actual point addition between the specified projective symmetric quotients is an immersion.
Source: Schoen (1988), printed p. 12; SGA 1, Exposé V, §1, invariant affine quotient charts. -/
theorem s2t_branch_projective_immersion (C P B : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (n + 1) σ ≫ γ = γ)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left :=
  s2t_branch_projective_immersion_aux C P B n b π γ hπinv hπquot hγinv hγquot a ha

example (C P B : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (n + 1) σ ≫ γ = γ)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left :=
  s2t_branch_projective_immersion C P B n b π γ hπinv hπquot hγinv hγquot a ha

#print axioms s2t_branch_projective_immersion
end HodgeLean.Foundations.Program
