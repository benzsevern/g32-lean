import HodgeLean.Foundations.Program.SchoenTowerL1aLiftedAction
import HodgeLean.Foundations.Program.SchoenTowerOverSections

/-! # Parameter actions on actual restricted ordered charts

Implication from the actual quotient permutation lifts and curve-coordinate
factorizations to the parameter permutation equations on sections.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Pullbacks of the same curve parameter along the actual coordinate maps
are permuted by the actual restricted section action.
Source: Schoen (1988), Lemma 2.2, printed p. 13, ordered local parameters. -/
theorem s2v_l1a_chart_parameter_action
    (X U Z : Over (Spec ↧ℂ)) (n : ℕ)
    (u : U ⟶ Z) [Mono u] (v : X ⟶ g3_power Z n) [Mono v]
    (ρ : Equiv.Perm (Fin n) → (X ⟶ X))
    (hρv : ∀ g, ρ g ≫ v = v ≫ s2_permute Z n g)
    (a : Fin n → (X ⟶ U)) (ha : ∀ i, a i ≫ u = v ≫ g3_proj Z n i)
    (z : Γ(U.left, ⊤)) :
    let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z n) v ρ hρv
    let act' := ((Over.forget (Spec ↧ℂ)).mapAut X).comp act
    letI := s2_schemeSectionAction X.left (Equiv.Perm (Fin n)) act'
    ∀ (g : Equiv.Perm (Fin n)) (i : Fin n),
      g • (a i).left.appTop.hom z = (a (g i)).left.appTop.hom z := by
  dsimp only
  intro g i
  have hmaps : ρ g⁻¹ ≫ a i = a (g i) := by
    apply (cancel_mono u).mp
    rw [Category.assoc, ha, ← Category.assoc, hρv, Category.assoc]
    simp only [s2_permute, s2_check_lift_proj]
    exact (ha (g i)).symm
  change (ρ g⁻¹).left.appTop ((a i).left.appTop z) = (a (g i)).left.appTop z
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  change (ρ g⁻¹ ≫ a i).left.appTop z = _
  rw [hmaps]

end HodgeLean.Foundations.Program
