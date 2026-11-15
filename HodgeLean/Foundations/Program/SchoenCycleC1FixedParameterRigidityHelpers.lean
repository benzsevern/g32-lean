import HodgeLean.Foundations.Program.SchoenCycleCurveJets
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Algebra.Equiv

/-! # Rigidity of scalar-preserving local actions fixing a parameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A scalar-preserving automorphism fixing a parameter of a Noetherian
local complex algebra with complex residue field is the identity. -/
theorem s2e_c1_local_automorphism_eq_one_of_fixed_parameter
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (τ : R ≃ₐ[ℂ] R) (hτ : τ t = t) : τ = 1 := by
  apply AlgEquiv.ext
  intro r
  change τ r = r
  apply sub_eq_zero.mp
  have hmem (N : ℕ) : τ r - r ∈ IsLocalRing.maximalIdeal R ^ N := by
    obtain ⟨c, hc⟩ := s2e_local_parameter_jet_expansion R φ t ht N r
    have hmap : Ideal.map τ.toRingHom (Ideal.span {t ^ N}) ≤ Ideal.span {t ^ N} := by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {τ (t ^ N)} ≤ Ideal.span {t ^ N}
      rw [map_pow, hτ]
    have hcτ := hmap (Ideal.mem_map_of_mem τ.toRingHom hc)
    change τ (r - ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ)) ∈ _ at hcτ
    simp only [map_sub, map_sum, map_mul, τ.commutes, map_pow, hτ] at hcτ
    have hh := (Ideal.span {t ^ N}).sub_mem hcτ hc
    rw [ht, Ideal.span_singleton_pow]
    convert hh using 1 <;> ring
  have hi : τ r - r ∈ ⨅ N : ℕ, IsLocalRing.maximalIdeal R ^ N :=
    by simpa only [Ideal.mem_iInf] using hmem
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hi
  exact hi

end HodgeLean.Foundations.Program
