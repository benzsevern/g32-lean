import HodgeLean.Foundations.Program.SchoenCycleC1OrbitRebaseHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-! # Choice of starting point in an actual deck fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Every point in a specified free exhaustive deck fibre can start its orbit. -/
theorem s2e_c1_deck_fibre_rebase {W B : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : m ≠ 0) (horder : End.of d ^ m = 1)
    (b : ComplexPoint B) (z : ComplexPoint W) (hz : Point.map β z = b)
    (hinj : Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z))
    (hex : ∀ v : ComplexPoint W, Point.map β v = b →
      ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom z = v)
    (w : ComplexPoint W) (hw : Point.map β w = b) :
    Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom w) ∧
      (∀ v : ComplexPoint W, Point.map β v = b →
        ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom w = v) := by
  haveI : IsIso d := by
    have h := s2e_generator_power_isIso d hm horder 1
    simpa only [pow_one] using h
  have hp (v : ComplexPoint W) : Point.map β (Point.map d v) = Point.map β v := by
    change (v ≫ d) ≫ β = v ≫ β
    rw [Category.assoc, hd]
  have hi : Function.Injective (fun t : Fin m => (Point.map d)^[t.val] z) := by
    simpa only [s2e_c1_point_map_power] using hinj
  have he : ∀ v : ComplexPoint W, Point.map β v = Point.map β z →
      ∃ t : Fin m, (Point.map d)^[t.val] z = v := by
    simpa only [s2e_c1_point_map_power, hz] using hex
  have h := s2e_c1_orbit_rebase (Point.map d) (Point.map β)
    (map_injective_of_mono d) hp m z hi he w (hw.trans hz.symm)
  simpa only [s2e_c1_point_map_power, hz] using h

/-- A free exhaustive degree-indexed orbit computes the cardinality of the
actual complex fibre. -/
theorem s2e_c1_deck_orbit_fibre_card {W B : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) (m : ℕ) (z : ComplexPoint W)
    (hinj : Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z))
    (hex : ∀ v : ComplexPoint W, Point.map β v = Point.map β z →
      ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom z = v) :
    Nat.card ((Point.map β) ⁻¹' {Point.map β z}) = m := by
  let F := (Point.map β) ⁻¹' {Point.map β z}
  have hpres (t : Fin m) : Point.map β (Point.map (End.of d ^ t.val).asHom z) = Point.map β z := by
    rw [← Point.map_comp_apply, s2e_c1_generator_power_over β d hd]
  let φ : Fin m → F := fun t => ⟨Point.map (End.of d ^ t.val).asHom z, hpres t⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro t u htu
      exact hinj (congrArg Subtype.val htu)
    · intro v
      obtain ⟨t, ht⟩ := hex v.val v.property
      exact ⟨t, Subtype.ext ht⟩
  simpa only [Nat.card_fin] using (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

end HodgeLean.Foundations.Program
