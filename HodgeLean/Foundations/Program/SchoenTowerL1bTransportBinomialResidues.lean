import HodgeLean.Foundations.Program.SchoenTowerL1bTransportEigenRatio
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalResidueTransport

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Multiplication of a rational function by an m-th power preserves its signed prime orders modulo m. -/
theorem s2v_l1b_transport_binomial_rescale
    {R E : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field E]
    (ρ : R →+* E) (hρ : Function.Injective ρ)
    {a b A B c d p : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (m : ℕ)
    (heq : ρ a / ρ b = (ρ c / ρ d) ^ m * (ρ A / ρ B)) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) := by
  have heq' : ρ a / ρ b = ρ (A * c ^ m) / ρ (B * d ^ m) := by
    rw [heq, map_mul, map_mul, map_pow, map_pow, div_pow]
    ring
  rw [s2v_l1b_kval_fraction_order_eq ρ hρ hp ha hb
    (mul_ne_zero hA (pow_ne_zero _ hc)) (mul_ne_zero hB (pow_ne_zero _ hd)) heq']
  exact s2v_l1b_kval_rescale_order_modEq hp hA hB hd hc m

/-- Binomial presentations of functions with the same deck character have the same prime residues. -/
theorem s2v_l1b_transport_same_character_residue
    {R F E : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field F] [Field E] [Algebra R F] [IsFractionRing R F] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (τ : E ≃ₐ[F] E) (hτ : orderOf τ = Module.finrank F E)
    {t u : E} (ht : t ≠ 0) (hu : u ≠ 0)
    {ξ : E} (hξ : ξ ≠ 0) (htξ : τ t = ξ * t) (huξ : τ u = ξ * u)
    {a b A B p : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (m : ℕ)
    (htm : t ^ m = algebraMap F E (algebraMap R F a) /
      algebraMap F E (algebraMap R F b))
    (hum : u ^ m = algebraMap F E (algebraMap R F A) /
      algebraMap F E (algebraMap R F B)) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) := by
  obtain ⟨c, d, hc, hd, htu⟩ :=
    s2v_l1b_transport_eigenfunction_fraction (R := R) τ hτ ht hu hξ htξ huξ
  let ρ := (algebraMap F E).comp (algebraMap R F)
  have hρ : Function.Injective ρ :=
    (algebraMap F E).injective.comp (IsFractionRing.injective R F)
  apply s2v_l1b_transport_binomial_rescale ρ hρ hp ha hb hA hB hc hd m
  change algebraMap F E (algebraMap R F a) /
    algebraMap F E (algebraMap R F b) = _
  rw [← htm, htu, mul_pow, hum]
  rfl

end HodgeLean.Foundations.Program
