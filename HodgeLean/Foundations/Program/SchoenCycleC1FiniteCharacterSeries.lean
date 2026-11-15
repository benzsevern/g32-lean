import HodgeLean.Foundations.Program.SchoenCycleC1FaithfulCharacterRoot
import HodgeLean.Foundations.Program.SchoenCycleC1FormalInvariantSeries

/-! # Formal quotient series for a faithful finite scalar action -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Simultaneous invariance under a faithful finite scalar character is
exactly unique expansion in the power given by the stabilizer cardinality. -/
theorem s2e_c1_finite_character_invariant_series
    {G k : Type*} [Group G] [Finite G] [CommRing k] [IsDomain k]
    (χ : G →* kˣ) (hχ : Function.Injective χ) (f : PowerSeries k) :
    (∀ g, PowerSeries.rescale (χ g : k) f = f) ↔
      ∃! u : PowerSeries k, PowerSeries.expand (Nat.card G) Nat.card_pos.ne' u = f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := s2e_c1_faithful_character_primitive_value χ hχ
    exact (s2e_c1_invariant_series_unique_expansion _ Nat.card_pos.ne' _ hg f).mp (hf g)
  · rintro ⟨u, rfl, _⟩ g
    have hg : (χ g : k) ^ Nat.card G = 1 := by
      have h := congrArg (fun x : G => (χ x : k)) (pow_card_eq_one' (x := g))
      simpa only [map_pow, Units.val_pow_eq_pow_val, map_one, Units.val_one] using h
    ext n
    rw [PowerSeries.coeff_rescale]
    by_cases hn : Nat.card G ∣ n
    · obtain ⟨r, rfl⟩ := hn
      rw [pow_mul, hg, one_pow, one_mul]
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ u hn, mul_zero]

end HodgeLean.Foundations.Program
