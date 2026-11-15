import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # The actual quotient pullback is fixed by the section action -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The section action fixes every actual section pulled back from the retained quotient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_quotient_sectionAction_fixes_pullback
    (X Y : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (U : Y.left.Opens) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    ∀ g (r : Γ(Y.left, U)),
      (MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)) g ((q.left.app U).hom r) =
        (q.left.app U).hom r := by
  letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  intro g r
  change ((a g⁻¹).left.appLE (q.left ⁻¹ᵁ U) (q.left ⁻¹ᵁ U)
    (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U)).hom
      ((q.left.app U).hom r) = (q.left.app U).hom r
  let W := q.left ⁻¹ᵁ U
  have he : q.left.appLE U W le_rfl ≫ (a g⁻¹).left.appLE W W
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U) = q.left.appLE U W le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have hq : (a g⁻¹).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv g⁻¹)
    simp only [hq]
  have h := congrArg (fun f : Γ(Y.left, U) ⟶ Γ(X.left, W) => f.hom r) he
  simpa only [W, Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply] using h

end HodgeLean.Foundations.Program
