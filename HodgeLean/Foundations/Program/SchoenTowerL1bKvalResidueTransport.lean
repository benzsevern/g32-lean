import HodgeLean.Foundations.Program.SchoenTowerL1bKvalPrimeOrders

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Integer prime orders scale under natural powers. -/
theorem s2v_l1b_kval_prime_order_pow
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {p a : R} (hp : Prime p) (k : ℕ) :
    ((emultiplicity p (a ^ k)).toNat : ℤ) =
      (k : ℤ) * ((emultiplicity p a).toNat : ℤ) := by
  rw [emultiplicity_pow hp, ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]

/-- Rational rescaling by an m-th power leaves every prime residue unchanged. -/
theorem s2v_l1b_kval_rescale_order_modEq
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {a b c d p : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (m : ℕ) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p (a * d ^ m)).toNat : ℤ) -
        ((emultiplicity p (b * c ^ m)).toNat : ℤ))
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) := by
  rw [s2v_l1b_kval_prime_order_mul hp ha (pow_ne_zero _ hd),
    s2v_l1b_kval_prime_order_mul hp hb (pow_ne_zero _ hc),
    s2v_l1b_kval_prime_order_pow hp, s2v_l1b_kval_prime_order_pow hp]
  apply Int.modEq_iff_dvd.mpr
  refine ⟨((emultiplicity p c).toNat : ℤ) - ((emultiplicity p d).toNat : ℤ), ?_⟩
  ring

/-- Equality of rational functions transports any prescribed prime-order residue. -/
theorem s2v_l1b_kval_fraction_residue_iff
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (ρ : R →+* K) (hρ : Function.Injective ρ)
    {a b c d p : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (heq : ρ a / ρ b = ρ c / ρ d) (m w : ℤ) :
    Int.ModEq m ((emultiplicity p a).toNat : ℤ)
        (((emultiplicity p b).toNat : ℤ) + w) ↔
      Int.ModEq m ((emultiplicity p c).toNat : ℤ)
        (((emultiplicity p d).toNat : ℤ) + w) := by
  have ho := s2v_l1b_kval_fraction_order_eq ρ hρ hp ha hb hc hd heq
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have he : ((emultiplicity p b).toNat : ℤ) + w - ((emultiplicity p a).toNat : ℤ) =
      ((emultiplicity p d).toNat : ℤ) + w - ((emultiplicity p c).toNat : ℤ) := by omega
  rw [he]

end HodgeLean.Foundations.Program
