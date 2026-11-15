import Mathlib.Basic.Complex.Basic
import HodgeLean.Foundations.Program.SchoenTowerI2aFiniteFieldPoints

/-! # Actual maps from retained tower stages to the initial base
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual tower maps compose to the initial base and retain every stated field-point square.
Source: Mathlib, Fin.induction and associativity of scheme morphisms. -/
theorem s2v_i2a_tower_initial_maps
    {K : Type} [Field K] (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, Spec (CommRingCat.of K) ⟶ (B i).left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc) :
    ∃ f : ∀ i, B i ⟶ B 0, ∀ i, η i ≫ (f i).left = η 0 := by
  have hex (i : Fin (r + 1)) : ∃ f : B i ⟶ B 0, η i ≫ f.left = η 0 := by
    induction i using Fin.induction with
    | zero => exact ⟨𝟙 _, Category.comp_id _⟩
    | succ j ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨b j ≫ f, ?_⟩
      change η j.succ ≫ ((b j).left ≫ f.left) = η 0
      rw [← Category.assoc, hη j, hf]
  choose f hf using hex
  exact ⟨f, hf⟩

end HodgeLean.Foundations.Program
