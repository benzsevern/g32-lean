import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.Algebra.Group.Commute.Units

/-! Finite-order algebraic endomorphisms give their actual complex-point homeomorphisms. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem finite_order_point_homeomorph (X : Over (Spec ↧ℂ)) (f : X ⟶ X)
    (m : ℕ) (hm : 0 < m) (hpow : End.of f ^ m = 1) :
    ∃ H : ComplexPoint X ≃ₜ ComplexPoint X, ∀ x, H x = Point.map f x := by
  letI : IsIso f := (CategoryTheory.isUnit_iff_isIso (End.of f)).mp
    (IsUnit.of_pow_eq_one hpow (Nat.ne_of_gt hm))
  refine ⟨{
    toFun := Point.map f
    invFun := Point.map (inv f)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := Point.continuous_map f
    continuous_invFun := Point.continuous_map (inv f) }, fun _ => rfl⟩
  · intro x
    change (x ≫ f) ≫ inv f = x
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · intro x
    change (x ≫ inv f) ≫ f = x
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem transported_finite_order_point_homeomorph
    {N W : Over (Spec ↧ℂ)} (e : N ≅ W) (f : N ⟶ N) (g : W ⟶ W)
    (he : f ≫ e.hom = e.hom ≫ g)
    (m : ℕ) (hm : 0 < m) (hpow : End.of f ^ m = 1) :
    ∃ H : ComplexPoint W ≃ₜ ComplexPoint W, ∀ x, H x = Point.map g x := by
  have hc : e.inv ≫ f ≫ e.hom = g := by
    rw [he, e.inv_hom_id_assoc]
  have hg := s2e_c1_transport_generator_order e.symm f m hpow
  change End.of (e.inv ≫ f ≫ e.hom) ^ m = 1 at hg
  rw [hc] at hg
  exact finite_order_point_homeomorph W g m hm hg

#print axioms finite_order_point_homeomorph
#print axioms transported_finite_order_point_homeomorph
end HodgeLean.Foundations.QuotientDuality
