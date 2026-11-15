import HodgeLean.Foundations.Program.SchoenCycleC1WeightedPrincipalUnit
import HodgeLean.Foundations.Program.SchoenCycleC1SignedWeightedPowerFactor
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The exact weighted ideal power and a common signed residue produce a
unit coefficient after rational rescaling, over an arbitrary domain. -/
theorem s2e_c1_weighted_signed_unit
    {R K J : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Fintype J]
    (g : J → R) (hg : ∀ j, g j ≠ 0) (k : J → ℕ) (n : J → ℤ)
    (E : R) (s : ℤ) (m : ℕ) (hm : 0 < m)
    (hn : ∀ j, (m : ℤ) ∣ n j - s * (k j : ℤ))
    (hI : (∏ j, (Ideal.span {g j}) ^ k j) = (Ideal.span {E}) ^ m) (u : Rˣ) :
    ∃ (a : K) (v : Rˣ), a ≠ 0 ∧
      algebraMap R K (u : R) * ∏ j, (algebraMap R K (g j)) ^ n j =
        a ^ m * algebraMap R K (v : R) := by
  obtain ⟨v, hv⟩ := s2e_c1_weighted_principal_unit g k E m hI
  have hprod : (∏ j, g j ^ k j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hg j)
  have hE : E ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_of_gt hm), mul_zero] at hv
    exact hprod hv
  have hmap (x : R) (hx : x ≠ 0) : algebraMap R K x ≠ 0 :=
    fun h => hx ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  obtain ⟨a, ha, hfactor⟩ := s2e_c1_signed_weighted_power_factor
    (fun j => algebraMap R K (g j)) (fun j => hmap _ (hg j)) k n s m hn
  have hweighted : (∏ j, (algebraMap R K (g j)) ^ k j) =
      algebraMap R K (v : R) * (algebraMap R K E) ^ m := by
    simpa only [map_prod, map_pow, map_mul] using congrArg (algebraMap R K) hv
  have hpow (x : K) : (x ^ m) ^ s = (x ^ s) ^ m := by
    rw [← zpow_natCast x m, ← zpow_mul, mul_comm (m : ℤ) s, zpow_mul, zpow_natCast]
  have hvpow : algebraMap R K ((v ^ s : Rˣ) : R) = (algebraMap R K (v : R)) ^ s := by
    change ((Units.map (algebraMap R K).toMonoidHom (v ^ s) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨a * (algebraMap R K E) ^ s, u * v ^ s,
    mul_ne_zero ha (zpow_ne_zero _ (hmap E hE)), ?_⟩
  change algebraMap R K (u : R) * ∏ j, (algebraMap R K (g j)) ^ n j =
    (a * (algebraMap R K E) ^ s) ^ m *
      algebraMap R K ((u : R) * ((v ^ s : Rˣ) : R))
  rw [hfactor, hweighted, mul_zpow, hpow, mul_pow, map_mul, hvpow]
  ring

end HodgeLean.Foundations.Program
