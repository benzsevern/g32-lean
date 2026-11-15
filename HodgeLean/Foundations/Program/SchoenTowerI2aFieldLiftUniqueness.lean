import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts

/-! # Uniqueness of retained field lifts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two lifts of the same dominant field point through the retained Cartier universal modification are equal.
Source: Mathlib, the Cartier universal property and s2_dominant_fieldPoint_cartier. -/
theorem s2v_i2a_retained_field_lift_unique
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ B.left) [IsDominant η]
    (θ θ' : Spec (CommRingCat.of K) ⟶ B'.left)
    (hθ : θ ≫ b.left = η) (hθ' : θ' ≫ b.left = η) : θ = θ' := by
  let T := Over.mk (η ≫ B.hom)
  let f : T ⟶ B := Over.homMk η
  let v : T ⟶ B' := Over.homMk θ (by
    rw [← Over.w b, ← Category.assoc, hθ]
    rfl)
  let w : T ⟶ B' := Over.homMk θ' (by
    rw [← Over.w b, ← Category.assoc, hθ']
    rfl)
  obtain ⟨_, _, huniq⟩ := huniv T f (s2_dominant_fieldPoint_cartier η I hI)
  exact congrArg Over.Hom.left
    ((huniq v (Over.OverMorphism.ext hθ)).trans
      (huniq w (Over.OverMorphism.ext hθ')).symm)

end HodgeLean.Foundations.Program
