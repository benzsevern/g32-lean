import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

/-! # Actual group actions on invariant chart restrictions

Implication from permutation lifts through a monomorphism to the actual
restricted automorphism group action. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Specified lifts of an automorphism action through a monomorphism form
an actual action by automorphisms, with the specified maps as their homs.
Source: Mac Lane, Categories for the Working Mathematician, I.5, monomorphisms and cancellation. -/
def s2v_l1a_liftedAction
    {C : Type*} [Category C] {X V : C} {G : Type*} [Group G]
    (a : G →* Aut X) (v : V ⟶ X) [Mono v]
    (ρ : G → (V ⟶ V))
    (hρ : ∀ g, ρ g ≫ v = v ≫ (a g).asIso.hom) : G →* Aut V := by
  have hmul (g h : G) : ρ (g * h) = ρ h ≫ ρ g := by
    apply (cancel_mono v).mp
    rw [hρ, Category.assoc, hρ, ← Category.assoc, hρ, Category.assoc]
    rw [map_mul]
    rfl
  have hone : ρ 1 = 𝟙 V := by
    apply (cancel_mono v).mp
    rw [hρ, map_one]
    simp
  let e (g : G) : V ≅ V :=
    { hom := ρ g
      inv := ρ g⁻¹
      hom_inv_id := by rw [← hmul, inv_mul_cancel, hone]
      inv_hom_id := by rw [← hmul, mul_inv_cancel, hone] }
  refine { toFun := fun g => Aut.of (e g), map_one' := ?_, map_mul' := ?_ }
  · apply Aut.ext
    apply Iso.ext
    exact hone
  · intro g h
    apply Aut.ext
    apply Iso.ext
    exact hmul g h

end HodgeLean.Foundations.Program
