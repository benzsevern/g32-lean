import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerDominance

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A birational retained map induces an isomorphism on the actual generic fields. -/
theorem s2v_l1b_birational_functionFieldPullback_isIso
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (hf : zmtiso_IsBirational f) :
    IsIso (s2v_l1b_functionFieldPullback f) := by
  haveI := hf.2
  dsimp only [s2v_l1b_functionFieldPullback]
  infer_instance

/-- The retained Cartier universal property makes the actual base modification birational. -/
theorem s2v_l1b_retained_cartier_birational
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U)))
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f) :
    zmtiso_IsBirational b.left := by
  obtain ⟨_, _, _, hb⟩ := s2_cartierUniversal_genericLift B' B b I
    (s2v_l1b_cartier_support_ne_top B' B b I hcartier) huniv
  exact hb

/-- Each retained Cartier modification gives an isomorphism of its actual function fields. -/
theorem s2v_l1b_retained_cartier_field_isIso
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) [IsDominant b.left] (I : B.left.IdealSheafData)
    (hcartier : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U)))
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f) :
    IsIso (s2v_l1b_functionFieldPullback b.left) := by
  exact s2v_l1b_birational_functionFieldPullback_isIso b.left
    (s2v_l1b_retained_cartier_birational B' B b I hcartier huniv)

end HodgeLean.Foundations.Program
