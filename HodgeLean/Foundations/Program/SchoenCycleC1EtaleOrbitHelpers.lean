import HodgeLean.Foundations.Program.SchoenCycleC1EtaleCardHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1TupleHelpers

/-! # Fibre orbits on the actual integral finite etale cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Faithfulness of generator powers and one degree-sized fibre supply
free exhaustive degree-indexed orbits on every finite etale fibre. -/
theorem s2e_c1_etale_fibre_orbit_of_faithful_powers
    (m : ℕ) (hm : 0 < m) (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsIntegral Y.left] [Smooth Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (d : X ⟶ X) (hd : d ≫ f = f) (horder : End.of d ^ m = 1)
    (hfaith : ∀ n, n < m → End.of d ^ n = 1 → n = 0)
    (y₀ : ComplexPoint Y) (hcard : Nat.card ((Point.map f) ⁻¹' {y₀}) = m) :
    ∀ y : ComplexPoint Y, ∃ z : ComplexPoint X, Point.map f z = y ∧
      Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z) ∧
      (∀ t : Fin m, Point.map f (Point.map (End.of d ^ t.val).asHom z) = y) ∧
      (∀ v : ComplexPoint X, Point.map f v = y →
        ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom z = v) := by
  classical
  intro y
  obtain ⟨z, hz⟩ := s2e_c11_finite_surjective_complex_points X Y f y
  have hperiod : Function.IsPeriodicPt (Point.map d) m z := by
    change (Point.map d)^[m] z = z
    rw [s2e_c1_point_map_power, horder]
    rfl
  have hreturn (n : ℕ) (hn : n < m) (hnz : (Point.map d)^[n] z = z) : n = 0 := by
    have hdz : Point.map (End.of d ^ n).asHom z = z := by
      rw [← s2e_c1_point_map_power]
      exact hnz
    have he := s2e_c1_etale_deck_eq_id_of_fixed_point X Y f (End.of d ^ n).asHom
      (s2e_c1_generator_power_over f d hd n) z hdz
    exact hfaith n hn (End.ext he)
  have hi : Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z) := by
    simpa only [s2e_c1_point_map_power] using
      s2e_c1_periodic_orbit_injective (Point.map d) z m hm hperiod hreturn
  have hpres (t : Fin m) : Point.map f (Point.map (End.of d ^ t.val).asHom z) = y := by
    rw [← Point.map_comp_apply, s2e_c1_generator_power_over f d hd]
    exact hz
  let F := (Point.map f) ⁻¹' {y}
  have hfinite : Set.Finite F := (s2e_c1_finite_etale_analytic_cover X Y f).2 y
  letI : Fintype F := hfinite.fintype
  let φ : Fin m → F := fun t => ⟨Point.map (End.of d ^ t.val).asHom z, hpres t⟩
  have hφinj : Function.Injective φ := by
    intro t u htu
    exact hi (congrArg Subtype.val htu)
  have hcy : Nat.card F = m :=
    (s2e_c1_finite_etale_fibre_card_eq X Y f y y₀).trans hcard
  have hcy' : Fintype.card F = m := by simpa only [Nat.card_eq_fintype_card] using hcy
  have hφsurj : Function.Surjective φ :=
    ((Fintype.bijective_iff_injective_and_card φ).mpr
      ⟨hφinj, by simpa only [Fintype.card_fin] using hcy'.symm⟩).2
  refine ⟨z, hz, hi, hpres, ?_⟩
  intro v hv
  obtain ⟨t, ht⟩ := hφsurj ⟨v, hv⟩
  exact ⟨t, congrArg Subtype.val ht⟩

end HodgeLean.Foundations.Program
