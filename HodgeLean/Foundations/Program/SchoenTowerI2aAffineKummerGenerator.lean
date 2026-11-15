import HodgeLean.Foundations.Program.SchoenTowerI2aKummerGenerator
import HodgeLean.Foundations.Program.SchoenTowerI2aKummerDenominators
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldRescaling

/-! # An integral Kummer generator over the actual affine base
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A cyclic Galois extension of the coefficient fraction field has an integral primitive eigenvector over the actual affine coefficient ring.
Source: Mathlib, cyclic Kummer theory, integral binomial roots and fraction-field denominator clearing. -/
theorem s2v_i2a_affine_integral_kummer_generator
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] [FiniteDimensional F K] [IsGalois F K]
    (m : ℕ) (hm : 0 < m) (ζ : R) (hζ : IsPrimitiveRoot (algebraMap R F ζ) m)
    (d : K ≃ₐ[F] K) (hd : orderOf d = m)
    (hcyc : ∀ σ : K ≃ₐ[F] K, σ ∈ Subgroup.zpowers d) :
    ∃ (v : K) (a : R), v ≠ 0 ∧ IsIntegral R v ∧
      d v = algebraMap R K ζ * v ∧ v ^ m = algebraMap R K a ∧
      Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤ := by
  obtain ⟨v, a, hvne, hdv, hvpow, hgen⟩ := s2v_i2a_cyclic_kummer_generator m hm
    (algebraMap R F ζ) hζ d hd hcyc
  obtain ⟨s, b, hs, hpow⟩ := s2v_i2a_clear_kummer_denominator (R := R) m hm v a hvpow
  let w := algebraMap R K s * v
  have hwdiv : w / algebraMap R K s = v := by
    dsimp only [w]
    exact mul_div_cancel_left₀ v hs
  have hgenR : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤ := by
    rw [s2v_i2a_fraction_base_generated_field (F := F)]
    exact hgen
  have hscale := s2v_i2a_rescaled_generator_field (algebraMap R K) w s hs
  rw [hwdiv] at hscale
  refine ⟨w, b, mul_ne_zero hs hvne, s2v_i2a_binomial_integral m hm b w hpow,
    ?_, hpow, hscale.symm.trans hgenR⟩
  change d (algebraMap R K s * v) = algebraMap R K ζ * (algebraMap R K s * v)
  have hfix : d (algebraMap R K s) = algebraMap R K s := by
    rw [IsScalarTower.algebraMap_apply R F K, d.commutes]
  rw [map_mul, hfix, hdv, ← IsScalarTower.algebraMap_apply R F K]
  ac_rfl

/-- Denominator rescaling makes a nonzero eigenvector integral without changing its generated original subfield.
Source: Mathlib, IsIntegral.exists_multiple_integral_of_isLocalization and scalar multiplication of eigenvectors. -/
theorem s2v_i2a_integral_eigenvector_rescaling
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] [FiniteDimensional F K]
    (hinj : Function.Injective (algebraMap R K)) (ζ : R)
    (d : K ≃ₐ[R] K) (v : K) (hv : v ≠ 0)
    (hdv : d v = algebraMap R K ζ * v) :
    ∃ w : K, w ≠ 0 ∧ IsIntegral R w ∧ d w = algebraMap R K ζ * w ∧
      Subfield.closure (Set.range (algebraMap R K) ∪ {w}) =
        Subfield.closure (Set.range (algebraMap R K) ∪ {v}) := by
  obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (M := nonZeroDivisors R) (Rₘ := F) v (Algebra.IsIntegral.isIntegral (R := F) v)
  have hsne : algebraMap R K (s : R) ≠ 0 := by
    intro hzero
    have hszero : (s : R) = 0 := hinj (hzero.trans (map_zero _).symm)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp s.property) hszero
  let w : K := algebraMap R K (s : R) * v
  have hwdiv : w / algebraMap R K (s : R) = v := mul_div_cancel_left₀ v hsne
  have hfield := s2v_i2a_rescaled_generator_field (algebraMap R K) w (s : R) hsne
  rw [hwdiv] at hfield
  refine ⟨w, mul_ne_zero hsne hv, ?_, ?_, hfield.symm⟩
  · simpa only [Submonoid.smul_def, Algebra.smul_def] using hs
  · dsimp only [w]
    rw [map_mul, d.commutes, hdv]
    ac_rfl

end HodgeLean.Foundations.Program
