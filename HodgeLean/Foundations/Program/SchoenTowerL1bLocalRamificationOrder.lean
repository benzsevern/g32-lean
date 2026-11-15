import HodgeLean.Foundations.Program.SchoenTowerL1bLocalMultiplicityOrder
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalBinomialOrder
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A compatible expansion detecting the prime divisor gives the ramification
order equation for any nonzero binomial generator fraction. -/
theorem s2v_l1b_local_ramification_order
    {R E K L : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field E] [Field K] [Field L]
    (ρ : R →+* E) (ψ : E →+* L) (ι : PowerSeries K →+* L)
    (β : R →+* PowerSeries K) (hι : Function.Injective ι)
    (p : R) (hp : Prime p)
    (hlocal : ∀ v : R, ¬ p ∣ v → (β v).constantCoeff ≠ 0)
    (hbase : ∀ v : R, ψ (ρ v) = ι (β v))
    (t : E) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hβa : β a ≠ 0) (hβb : β b ≠ 0)
    (F G : PowerSeries K) (hF : F ≠ 0) (hG : G ≠ 0)
    (m : ℕ) (hpow : t ^ m = ρ a / ρ b)
    (ht : ψ t = ι F / ι G) :
    (m : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) =
      ((β p).order.toNat : ℤ) *
        (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) := by
  have haord := congrArg ENat.toNat
    (s2v_l1b_local_multiplicity_order β p a
      (FiniteMultiplicity.of_prime_left hp ha) hlocal)
  have hbord := congrArg ENat.toNat
    (s2v_l1b_local_multiplicity_order β p b
      (FiniteMultiplicity.of_prime_left hp hb) hlocal)
  simp only [ENat.toNat_mul] at haord hbord
  have hh := s2v_l1b_local_binomial_order ρ ψ ι hι t a b F G (β a) (β b)
    hF hG hβa hβb m hpow ht (hbase a) (hbase b)
  rw [haord, hbord, Nat.cast_mul, Nat.cast_mul] at hh
  rw [hh]
  ring

end HodgeLean.Foundations.Program
