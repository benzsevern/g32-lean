import HodgeLean.Foundations.QuotientDuality.RetainedCoordinateIsomorphisms
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The finite algebraic group of sum-zero retained coordinate transformations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ)

def retainedCoordinateSubgroup : Subgroup (Aut (g3_power Y n)) where
  carrier := {f | ∃ (v : Fin n → ZMod S.m), (∑ i, v i) = 0 ∧
    ∃ σ : Equiv.Perm (Fin n), f.asIso.hom = s2_action S Y a e n v σ}
  one_mem' := by
    refine ⟨0, by simp, 1, ?_⟩
    exact (s2_coordinateAction_laws S Y a e ha1 hamul n).1.symm
  mul_mem' := by
    rintro f g ⟨v, hv, σ, hσ⟩ ⟨w, hw, τ, hτ⟩
    refine ⟨fun i => v i + w (σ.symm i), ?_, σ * τ, ?_⟩
    · rw [Finset.sum_add_distrib, Equiv.sum_comp, hv, hw, add_zero]
    · change g.asIso.hom ≫ f.asIso.hom = _
      rw [hτ, hσ]
      exact (s2_coordinateAction_laws S Y a e ha1 hamul n).2 w v τ σ
  inv_mem' := by
    rintro f ⟨v, hv, σ, hσ⟩
    refine ⟨fun i => -v (σ i), ?_, σ⁻¹, ?_⟩
    · rw [Finset.sum_neg_distrib, Equiv.sum_comp, hv, neg_zero]
    · have he : f.asIso = retainedCoordinateIso S Y a e ha1 hamul n v σ := Iso.ext hσ
      change f.asIso.inv = _
      rw [he]
      rfl

theorem retainedCoordinateSubgroup_finite :
    (retainedCoordinateSubgroup S Y a e ha1 hamul n : Set (Aut (g3_power Y n))).Finite := by
  classical
  let I := {v : Fin n → ZMod S.m // (∑ i, v i) = 0} × Equiv.Perm (Fin n)
  let F : I → Aut (g3_power Y n) := fun p =>
    Aut.of (retainedCoordinateIso S Y a e ha1 hamul n p.1.1 p.2)
  apply (Set.finite_range F).subset
  rintro f ⟨v, hv, σ, hσ⟩
  refine ⟨(⟨v, hv⟩, σ), ?_⟩
  apply Aut.ext
  apply Iso.ext
  exact hσ.symm

#print axioms retainedCoordinateSubgroup
#print axioms retainedCoordinateSubgroup_finite
end HodgeLean.Foundations.QuotientDuality
