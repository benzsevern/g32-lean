import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # Linearity over the actual quotient section ring -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual quotient-chart action commutes with scalars from sections downstairs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, invariant affine quotients. -/
theorem s2e_quotient_sectionAction_base_smulComm
    (X Y : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (U : Y.left.Opens) :
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    SMulCommClass G Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := by
  let W := q.left ⁻¹ᵁ U
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  refine ⟨fun u c b => ?_⟩
  let ρ := (a u⁻¹).left.appLE W W
    (s2e_step1_action_preimage X Y q (a u⁻¹) (hinv u⁻¹) U)
  have he : q.left.app U ≫ ρ = q.left.app U := by
    calc
      q.left.app U ≫ ρ = q.left.appLE U W le_rfl ≫ ρ := by
        rw [Scheme.Hom.appLE_eq_app]
      _ = ((a u⁻¹).left ≫ q.left).appLE U W _ := by
        dsimp only [ρ]
        rw [Scheme.Hom.appLE_comp_appLE]
      _ = q.left.appLE U W le_rfl := by
        congr 1
        exact congrArg Over.Hom.left (hinv u⁻¹)
      _ = q.left.app U := Scheme.Hom.appLE_eq_app q.left
  change ρ.hom ((q.left.app U).hom c * b) = (q.left.app U).hom c * ρ.hom b
  rw [map_mul]
  congr 1
  exact congrArg (fun t : Γ(Y.left, U) ⟶ Γ(X.left, W) => t.hom c) he

#print axioms s2e_quotient_sectionAction_base_smulComm
end HodgeLean.Foundations.Program
