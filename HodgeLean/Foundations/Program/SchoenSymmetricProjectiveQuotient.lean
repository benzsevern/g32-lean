import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import HodgeLean.Foundations.Program.SchoenProjectiveActionQuotient
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The actual symmetric permutation quotient is an integral projective scheme with finite quotient map, complex orbit fibres and arbitrary-target descent. -/
theorem s2_symmetricPower_projectiveQuotient (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ∃ (B : Over (Spec ↧ℂ)) (γ : g3_power X n ⟶ B),
      IsIntegral B.left ∧ IsProjective B.hom ∧ IsFinite γ.left ∧
      Function.Surjective (Point.map γ) ∧
      (∀ σ, s2_permute X n σ ≫ γ = γ) ∧
      (∀ x y : ComplexPoint (g3_power X n), Point.map γ x = Point.map γ y ↔
        ∃ σ, Point.map (s2_permute X n σ) x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : g3_power X n ⟶ T),
        (∀ σ, s2_permute X n σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f) ∧
      zmtiso_IsNormal B.left := by
  letI := spec_g3b_geometricallyIntegral X
  obtain ⟨B, γ, hB, hp, hf, hs, hi, ho, hd, hn⟩ :=
    s2_finiteAction_projectiveQuotient (g3_power X n) (Equiv.Perm (Fin n))
      (s2_symmetricPowerAction X n)
  exact ⟨B, γ, hB, hp, hf, hs, hi, ho, hd, hn inferInstance⟩

end HodgeLean.Foundations.Program
