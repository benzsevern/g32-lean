import HodgeLean.Foundations.Program.SchoenTowerBranchSectionExtension
import HodgeLean.Foundations.Program.SchoenTowerQuotientSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Insertion into affine categorical symmetric quotients is surjective on sections.
Source: SGA 1, Exposé V, §1; compatible coordinate retractions for point insertion. -/
theorem s2t_branch_affine_sections_surjective (C P B : Over (Spec ↧ℂ)) (n : ℕ)
    (b : ComplexPoint C) (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    Function.Surjective a.left.appTop := by
  intro p
  have hp (σ) : (s2_permute C n σ).left.appTop (π.left.appTop p) = π.left.appTop p := by
    have he := congrArg (fun f : g3_power C n ⟶ P => f.left.appTop p) (hπinv σ)
    simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using he
  obtain ⟨q, hq, hqi⟩ := s2t_branch_invariant_section_extension C n b (π.left.appTop p) hp
  obtain ⟨r, hr⟩ := s2t_quotient_section_desc C B (n + 1) γ hγquot q hq
  refine ⟨r, s2t_quotient_sections_injective C P n π hπinv hπquot ?_⟩
  change s2t_overSectionsAlgHom π (s2t_overSectionsAlgHom a r) = π.left.appTop p
  rw [s2t_overSectionsAlgHom_comp_apply, ha, ← s2t_overSectionsAlgHom_comp_apply]
  change (s2c_branchInsertion C n b).left.appTop (γ.left.appTop r) = π.left.appTop p
  rw [hr, hqi]

/-- The actual point-addition map between affine symmetric quotients is an immersion.
Source: Schoen (1988), printed p. 12, branch insertion; SGA 1, Exposé V, §1. -/
theorem s2t_branch_affine_immersion_aux (C P B : Over (Spec ↧ℂ))
    [IsAffine P.left] [IsAffine B.left] (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left :=
  IsClosedImmersion.of_surjective_of_isAffine a.left
    (s2t_branch_affine_sections_surjective C P B n b π γ hπinv hπquot hγquot a ha)

end HodgeLean.Foundations.Program
