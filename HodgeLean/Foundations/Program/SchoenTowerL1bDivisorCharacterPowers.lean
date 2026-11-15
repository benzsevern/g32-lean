import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckPowers
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationEigenOrder
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportQuotientAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Natural powers of the original action are actual powers of its endomorphisms. -/
theorem s2v_l1b_divisor_action_pow
    {D : Type*} [Category D] (X : D) (G : Type*) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (g : G) (n : ℕ) :
    a (g ^ n) = (End.of (a g) ^ n).asHom := by
  induction n with
  | zero => simpa only [pow_zero, End.one_asHom] using ha1
  | succ n ih => rw [pow_succ, hamul, ih, pow_succ, End.mul_asHom]

/-- A specified eigenfunction has the iterated character under the corresponding action power. -/
theorem s2v_l1b_divisor_character_power
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) (τ : X.left.functionField ≃+* X.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.left.fromSpecStalk (genericPoint X.left) =
        X.left.fromSpecStalk (genericPoint X.left) ≫ (a g).left)
    (u ξ : X.left.functionField) (hξ : τ ξ = ξ) (hu : τ u = ξ * u) (n : ℕ) :
    letI : IsIso (a (g ^ n)).left := by
      change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul (g ^ n)).asIso.hom.left)
      infer_instance
    s2v_l1b_functionFieldPullback (a (g ^ n)).left u = ξ ^ n * u := by
  letI : IsIso (a (g ^ n)).left := by
    change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul (g ^ n)).asIso.hom.left)
    infer_instance
  change s2v_l1b_functionFieldPullback (a (g ^ n)).left u = ξ ^ n * u
  have hp := s2v_l1b_deck_generic_powers X.left (a g).left τ hτ n
  have he : (End.of (a g).left ^ n).asHom = (a (g ^ n)).left := by
    rw [s2v_l1b_divisor_action_pow X G a ha1 hamul]
    clear hp
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, Over.comp_left, ih]
  rw [he] at hp
  have hmap := s2v_l1b_transport_symmetry_eq_pullback X.left (a (g ^ n)).left
    (τ ^ n).toRingHom hp
  rw [← hmap]
  exact s2v_l1b_rotation_eigenfunction_iterate τ hξ hu n

end HodgeLean.Foundations.Program
