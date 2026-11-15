import HodgeLean.Foundations.Program.SchoenCycleC1FixedStalkCompositionHelpers
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # The actual finite action on a fixed stalk -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Inverse pullback of an actual group action fixing a scheme point
constructs a group homomorphism on its stalk over the specified complex scalars. -/
theorem s2e_c1_actual_fixed_stalk_action_hom
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : X.left) (hfixed : ∀ g, (a g).left p = p) :
    letI : Algebra ℂ (X.left.presheaf.stalk p) :=
      (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    ∃ ρ : G →* (X.left.presheaf.stalk p ≃ₐ[ℂ] X.left.presheaf.stalk p),
      ∀ g, (ρ g).toRingHom = s2e_fixed_point_stalkPullback X.left (a g⁻¹).left p (hfixed g⁻¹) := by
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  haveI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  have hex (g : G) := s2e_c1_fixed_point_stalk_algEquiv X (a g⁻¹) p (hfixed g⁻¹)
  choose τ hτ using hex
  refine ⟨{ toFun := τ, map_one' := ?_, map_mul' := ?_ }, hτ⟩
  · apply AlgEquiv.ext
    intro r
    change (τ 1).toRingHom r = r
    rw [hτ]
    simp only [inv_one, ha1, Over.id_left, s2e_c1_fixed_stalk_pullback_id, RingHom.id_apply]
  · intro g h
    apply AlgEquiv.ext
    intro r
    change (τ (g * h)).toRingHom r = (τ g).toRingHom ((τ h).toRingHom r)
    rw [hτ, hτ, hτ]
    simp only [mul_inv_rev, hamul]
    change s2e_fixed_point_stalkPullback X.left
      ((a g⁻¹).left ≫ (a h⁻¹).left) p _ r = _
    rw [s2e_c1_fixed_stalk_pullback_comp X.left (a g⁻¹).left (a h⁻¹).left p
      (hfixed g⁻¹) (hfixed h⁻¹), RingHom.comp_apply]

end HodgeLean.Foundations.Program
