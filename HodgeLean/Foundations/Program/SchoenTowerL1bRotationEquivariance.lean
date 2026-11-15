import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Scalar preservation and one exact eigenparameter determine the action on
all formal expansions when every element has a scalar remainder modulo that
parameter. -/
theorem s2v_l1b_rotation_expansion_equivariance
    {R K : Type*} [CommRing R] [CommRing K]
    (c : K →+* R) (ι : R →+* PowerSeries K)
    (hc : ∀ k, ι (c k) = PowerSeries.C k)
    (τ : R →+* R) (hτ : ∀ k, τ (c k) = c k)
    (u : R) (hu : ι u = PowerSeries.X) (ζ : K)
    (he : τ u = c ζ * u)
    (hdivision : ∀ v : R, ∃ k : K, ∃ w : R, v = c k + u * w) :
    ∀ v : R, ι (τ v) = PowerSeries.rescale ζ (ι v) := by
  have hcoeff (n : ℕ) (v : R) :
      PowerSeries.coeff n (ι (τ v)) = ζ ^ n * PowerSeries.coeff n (ι v) := by
    induction n generalizing v with
    | zero =>
      obtain ⟨k, w, rfl⟩ := hdivision v
      simp only [map_add, map_mul, hτ, he, hc, hu, mul_assoc,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_zero_C, add_zero, mul_zero, pow_zero, one_mul]
    | succ n ih =>
      obtain ⟨k, w, rfl⟩ := hdivision v
      simp only [map_add, map_mul, hτ, he, hc, hu, mul_assoc,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_of_ne_zero (Nat.succ_ne_zero n), zero_add]
      rw [ih, pow_succ']
      exact (mul_assoc _ _ _).symm
  intro v
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale]
  exact hcoeff n v

/-- A scalar splitting of the residue map and a principal residue kernel give
scalar remainders modulo the parameter. -/
theorem s2v_l1b_rotation_parameter_division
    {R K : Type*} [CommRing R] [CommRing K]
    (c : K →+* R) (ρ : R →+* K) (hρ : ∀ k, ρ (c k) = k)
    (u : R) (hker : RingHom.ker ρ = Ideal.span {u}) :
    ∀ v : R, ∃ k : K, ∃ w : R, v = c k + u * w := by
  intro v
  have hm : v - c (ρ v) ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, hρ, sub_self]
  rw [hker, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨ρ v, w, ?_⟩
  exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)

end HodgeLean.Foundations.Program
