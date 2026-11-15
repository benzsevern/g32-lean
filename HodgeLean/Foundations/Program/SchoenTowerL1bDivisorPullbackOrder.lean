import HodgeLean.Foundations.Program.SchoenTowerL1bLocalFractionOrder
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalMultiplicityOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A rational power equation computes the base divisor order from an actual local expansion. -/
theorem s2v_l1b_divisor_pullback_fraction_order
    {R T E K : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing T] [Field E] [Field K]
    (φ : R →+* T) (ρ : T →+* E) (hρ : Function.Injective ρ)
    (ι : T →+* PowerSeries K) (hι : Function.Injective ι)
    (p : R) (hp : Prime p)
    (hlocal : ∀ v : R, ¬ p ∣ v → (ι (φ v)).constantCoeff ≠ 0)
    (a b : T) (ha : a ≠ 0) (hb : b ≠ 0)
    (A B : R) (hA : A ≠ 0) (hB : B ≠ 0)
    (hφA : φ A ≠ 0) (hφB : φ B ≠ 0)
    (m : ℕ) (hpow : (ρ a / ρ b) ^ m = ρ (φ A) / ρ (φ B)) :
    (m : ℤ) * (((ι a).order.toNat : ℤ) - ((ι b).order.toNat : ℤ)) =
      ((ι (φ p)).order.toNat : ℤ) *
        (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) := by
  have hbE : ρ b ≠ 0 := fun h => hb (hρ (h.trans ρ.map_zero.symm))
  have hBE : ρ (φ B) ≠ 0 := fun h => hφB (hρ (h.trans ρ.map_zero.symm))
  have hcross : a ^ m * φ B = φ A * b ^ m := by
    apply hρ
    simpa only [map_mul, map_pow] using
      (div_eq_div_iff (pow_ne_zero m hbE) hBE).mp (by rwa [div_pow] at hpow)
  have hseries : (ι a) ^ m * ι (φ B) = ι (φ A) * (ι b) ^ m := by
    simpa only [map_mul, map_pow] using congrArg ι hcross
  have hord := s2v_l1b_local_fraction_order (ι a) (ι b) (ι (φ A)) (ι (φ B))
    (fun h => ha (hι (h.trans ι.map_zero.symm)))
    (fun h => hb (hι (h.trans ι.map_zero.symm)))
    (fun h => hφA (hι (h.trans ι.map_zero.symm)))
    (fun h => hφB (hι (h.trans ι.map_zero.symm))) m hseries
  have hoA := congrArg ENat.toNat
    (s2v_l1b_local_multiplicity_order (ι.comp φ) p A
      (FiniteMultiplicity.of_prime_left hp hA) hlocal)
  have hoB := congrArg ENat.toNat
    (s2v_l1b_local_multiplicity_order (ι.comp φ) p B
      (FiniteMultiplicity.of_prime_left hp hB) hlocal)
  simp only [RingHom.coe_comp, Function.comp_apply, ENat.toNat_mul] at hoA hoB
  rw [hord, hoA, hoB, Nat.cast_mul, Nat.cast_mul]
  ring

end HodgeLean.Foundations.Program
