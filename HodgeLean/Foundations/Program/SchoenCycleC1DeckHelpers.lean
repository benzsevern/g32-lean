import HodgeLean.Foundations.Program.SchoenCycleOrbitHelpers
import Mathlib.CategoryTheory.Conj

/-! # Transport of the retained deck generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transport preserves the specified power relation. -/
theorem s2e_c1_transport_generator_order {W N : Over (Spec ↧ℂ)}
    (e : W ≅ N) (d : N ⟶ N) (m : ℕ) (hd : End.of d ^ m = 1) :
    End.of (e.hom ≫ d ≫ e.inv) ^ m = 1 := by
  change e.symm.conj (End.of d) ^ m = 1
  rw [← e.symm.conj_pow, hd, map_one]

/-- Every power of an endomorphism over the base preserves its projection. -/
theorem s2e_c1_generator_power_over {W B : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) (n : ℕ) :
    (End.of d ^ n).asHom ≫ β = β := by
  induction n with
  | zero => exact Category.id_comp β
  | succ n ih =>
    rw [pow_succ]
    change d ≫ (End.of d ^ n).asHom ≫ β = β
    rw [ih, hd]

/-- Transported powers preserve the transported normalization projection. -/
theorem s2e_c1_transport_generator_power_over {W N B : Over (Spec ↧ℂ)}
    (e : W ≅ N) (β : N ⟶ B) (d : N ⟶ N) (hd : d ≫ β = β) (n : ℕ) :
    (End.of (e.hom ≫ d ≫ e.inv) ^ n).asHom ≫ (e.hom ≫ β) = e.hom ≫ β := by
  apply s2e_c1_generator_power_over
  simp only [Category.assoc, e.inv_hom_id_assoc, hd]

/-- Iteration on complex points agrees with the actual endomorphism power. -/
theorem s2e_c1_point_map_power {W : Over (Spec ↧ℂ)} (d : W ⟶ W)
    (n : ℕ) (z : ComplexPoint W) :
    (Point.map d)^[n] z = Point.map (End.of d ^ n).asHom z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

/-- A specified equivariant map intertwines every power of its generators. -/
theorem s2e_c1_equivariant_generator_power {X Y : Over (Spec ↧ℂ)}
    (w : X ⟶ Y) (dX : X ⟶ X) (dY : Y ⟶ Y)
    (hd : dX ≫ w = w ≫ dY) (n : ℕ) :
    (End.of dX ^ n).asHom ≫ w = w ≫ (End.of dY ^ n).asHom := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact (Category.id_comp w).trans (Category.comp_id w).symm
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change ((End.of dX ^ n).asHom ≫ dX) ≫ w =
      w ≫ (End.of dY ^ n).asHom ≫ dY
    rw [Category.assoc, hd, ← Category.assoc, ih, Category.assoc]

end HodgeLean.Foundations.Program
