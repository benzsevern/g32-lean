import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Insertion intertwines a permutation with its extension fixing the first slot. -/
theorem s2t_branchInsertion_permute (C : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (σ : Equiv.Perm (Fin h)) :
    s2_permute C h σ ≫ s2c_branchInsertion C h b =
      s2c_branchInsertion C h b ≫ s2_permute C (h + 1)
        ((finSuccEquiv h).trans ((Equiv.optionCongr σ).trans
          (finSuccEquiv h).symm)) := by
  apply s2_product_hom_ext (h + 1)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Category.assoc, s2c_branchInsertion, s2_permute, s2_check_lift_proj,
      Equiv.symm_trans_apply, Equiv.symm_symm, finSuccEquiv_zero,
      ← Equiv.optionCongr_symm, Equiv.optionCongr_apply, Option.map_none,
      finSuccEquiv_symm_none, Fin.cases_zero]
    rw [← Category.assoc]
    congr 1
    exact Subsingleton.elim _ _
  · simp only [Category.assoc, s2c_branchInsertion, s2_permute, s2_check_lift_proj,
      Equiv.symm_trans_apply, Equiv.symm_symm, finSuccEquiv_succ,
      ← Equiv.optionCongr_symm, Equiv.optionCongr_apply, Option.map_some,
      finSuccEquiv_symm_some, Fin.cases_succ]

/-- An invariant target map descends uniquely through the specified categorical quotient.
Source: SGA 1, Exposé V, §1, categorical quotient universal property. -/
theorem s2t_branch_descent_aux (C P B : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint C) (π : g3_power C h ⟶ P)
    (γ : g3_power C (h + 1) ⟶ B)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (h + 1) σ ≫ γ = γ) :
    ∃! a : P ⟶ B, π ≫ a = s2c_branchInsertion C h b ≫ γ := by
  apply hπquot
  intro σ
  rw [← Category.assoc, s2t_branchInsertion_permute, Category.assoc, hγinv]

end HodgeLean.Foundations.Program
