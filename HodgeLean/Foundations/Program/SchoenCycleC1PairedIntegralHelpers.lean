import HodgeLean.Foundations.Program.SchoenCycleC1KummerScaleHelpers
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Integral divided coordinates on paired blowup charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- The divided covering coordinate is integral over the chart ring even
when the exceptional parameter is not a unit in that ring. -/
theorem s2e_c1_paired_divided_coordinate_integral
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (x v u : R) (z : K) (a b m : ℕ) (hm : 0 < m)
    (hx : algebraMap R K x ≠ 0) (hab : a + b = m)
    (hz : z ^ m = algebraMap R K (x ^ a * (x * v) ^ b * u)) :
    IsIntegral R (z / algebraMap R K x) := by
  have hz' : z ^ m = (algebraMap R K x) ^ a *
      (algebraMap R K x * algebraMap R K v) ^ b * algebraMap R K u := by
    simpa only [map_mul, map_pow] using hz
  have hw := s2e_c1_paired_equation_divide
    (algebraMap R K x) (algebraMap R K v) z (algebraMap R K u) a b m hx hab hz'
  apply IsIntegral.of_pow hm
  rw [hw, ← map_pow, ← map_mul]
  exact isIntegral_algebraMap

/-- The divided coordinate defines a map from the residual Kummer algebra
into the actual integral closure, with the prescribed value in the field. -/
theorem s2e_c1_paired_divided_coordinate_map
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (x v u : R) (z : K) (a b m : ℕ) (hm : 0 < m)
    (hx : algebraMap R K x ≠ 0) (hab : a + b = m)
    (hz : z ^ m = algebraMap R K (x ^ a * (x * v) ^ b * u)) :
    ∃ Φ : AdjoinRoot (X ^ m - C (v ^ b * u) : R[X]) →ₐ[R] integralClosure R K,
      (Φ (AdjoinRoot.root _) : K) = z / algebraMap R K x := by
  let w : integralClosure R K := ⟨z / algebraMap R K x,
    s2e_c1_paired_divided_coordinate_integral x v u z a b m hm hx hab hz⟩
  have hw : (w : K) ^ m = algebraMap R K (v ^ b * u) := by
    have hz' : z ^ m = (algebraMap R K x) ^ a *
        (algebraMap R K x * algebraMap R K v) ^ b * algebraMap R K u := by
      simpa only [map_mul, map_pow] using hz
    simpa only [map_mul, map_pow] using s2e_c1_paired_equation_divide
      (algebraMap R K x) (algebraMap R K v) z (algebraMap R K u) a b m hx hab hz'
  have hroot : eval₂ (Algebra.ofId R (integralClosure R K)) w
      (X ^ m - C (v ^ b * u) : R[X]) = 0 := by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
    apply Subtype.ext
    exact hw
  refine ⟨AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) w hroot, ?_⟩
  rw [AdjoinRoot.liftAlgHom_root]

end HodgeLean.Foundations.Program
