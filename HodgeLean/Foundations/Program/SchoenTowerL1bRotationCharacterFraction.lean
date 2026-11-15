import HodgeLean.Foundations.Program.SchoenTowerL1bRotationChosenCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerField

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Character selection and a rational binomial presentation use the same field
generator, independently of any later choice of a prime of the base domain. -/
theorem s2v_l1b_rotation_character_fraction
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (τ : K ≃ₐ[F] K) (hτ : orderOf τ = Module.finrank F K)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Module.finrank F K)) :
    let ρ := (algebraMap F K).comp (algebraMap R F)
    ∃ (t : K) (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ t ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ Module.finrank F K = ρ a / ρ b ∧ τ t = ζ • t := by
  obtain ⟨t, ht, heigen, hpow, hgen⟩ :=
    s2v_l1b_rotation_degree_order_character_generator τ hτ hζ
  obtain ⟨c, hc⟩ := hpow
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R c
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [map_zero, zero_div] at hab
    have hc' : c = 0 := hab.symm
    rw [hc', map_zero] at hc
    exact pow_ne_zero _ ht hc.symm
  refine ⟨t, a, b, ha, hb', ht, ?_, ?_, heigen⟩
  · rw [s2v_l1b_fraction_field_generator, hgen]
    rfl
  · change t ^ Module.finrank F K =
      algebraMap F K (algebraMap R F a) / algebraMap F K (algebraMap R F b)
    rw [← map_div₀, hab]
    exact hc.symm

end HodgeLean.Foundations.Program
