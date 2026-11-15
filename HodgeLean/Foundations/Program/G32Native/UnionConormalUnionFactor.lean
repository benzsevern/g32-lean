import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Component factorizations through the supplied union -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The second component factors through a closed union defined by the kernel infimum. -/
lemma unionConormal_second_factor
    {V T T₁ T₂ : Scheme} (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t] (hunion : t.ker = t₁.ker ⊓ t₂.ker) :
    ∃ b : T₂ ⟶ T, b ≫ t = t₂ := by
  have hk : t.ker ≤ t₂.ker := hunion.trans_le inf_le_right
  exact ⟨IsClosedImmersion.lift t t₂ hk, IsClosedImmersion.lift_fac t t₂ hk⟩

end HodgeLean.Foundations.Program.G32Native
