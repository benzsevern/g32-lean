import Mathlib.RingTheory.Ideal.Cotangent

/-! # First-order equation relations from actual cotangent classes

The original quotient relation puts its equation error in the square of any ideal containing the immersion ideal.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.TubularEuler

theorem conormal_relation_error_mem_square
    {R J : Type*} [CommRing R] [Fintype J]
    (I M : Ideal R) (hIM : I ≤ M) (f : J → I) (g : I) (c : J → R)
    (hrel : I.toCotangent g = ∑ i, c i • I.toCotangent (f i)) :
    (g : R) - ∑ i, c i * (f i : R) ∈ M ^ 2 := by
  have heq : I.toCotangent g = I.toCotangent (∑ i, c i • f i) := by
    simpa only [map_sum, map_smul] using hrel
  have hsq := (I.toCotangent_eq).mp heq
  have hpow : I ^ 2 ≤ M ^ 2 := pow_le_pow_left' hIM 2
  have h := hpow hsq
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_eq_mul] using h

#print axioms conormal_relation_error_mem_square

end HodgeLean.Foundations.TubularEuler
