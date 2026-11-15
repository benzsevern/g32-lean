import HodgeLean.Foundations.Program.SchoenTowerI2aAffineKummerGenerator
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportCharacterRoot

/-! Integral generators with the common signed rotation character.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The common rotation sign selects an integral primitive generator over the actual coefficient ring. -/
theorem s2v_i2a_signed_affine_kummer_generator
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra ℂ R] [Algebra R F] [IsFractionRing R F]
    [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    [FiniteDimensional F K] [IsGalois F K]
    (m : ℕ) (hm : 0 < m) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (d : K ≃ₐ[F] K) (hd : orderOf d = m)
    (hcyc : ∀ σ : K ≃ₐ[F] K, σ ∈ Subgroup.zpowers d) :
    ∃ (v : K) (a : R), v ≠ 0 ∧ IsIntegral R v ∧
      d v = algebraMap R K (algebraMap ℂ R
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ)))) * v ∧
      v ^ m = algebraMap R K a ∧
      Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤ := by
  let χ : ℂ := Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ))
  let ψ : ℂ →+* F := (algebraMap R F).comp (algebraMap ℂ R)
  have hχ : IsPrimitiveRoot (algebraMap R F (algebraMap ℂ R χ)) m :=
    (s2v_l1b_signed_character_primitive m (by omega) s hs).map_of_injective ψ.injective
  exact s2v_i2a_affine_integral_kummer_generator m hm (algebraMap ℂ R χ) hχ d hd hcyc

end HodgeLean.Foundations.Program
