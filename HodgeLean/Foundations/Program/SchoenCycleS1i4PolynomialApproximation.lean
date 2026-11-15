import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticCoordinates

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_polynomial_approximation_of_local_generators
    {R : Type*} [CommRing R] [IsLocalRing R] (d : ℕ)
    (P : MvPolynomial (Fin d) ℂ →+* R) (e : R →+* ℂ)
    (he : ∀ c, e (P (MvPolynomial.C c)) = c)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => P (MvPolynomial.X i))))
    (N : ℕ) (a : R) :
    ∃ q : MvPolynomial (Fin d) ℂ, a - P q ∈ IsLocalRing.maximalIdeal R ^ N := by
  induction N generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    have hm : a - P (MvPolynomial.C (e a)) ∈ IsLocalRing.maximalIdeal R := by
      change ¬ IsUnit _
      intro hu
      have hz : e (a - P (MvPolynomial.C (e a))) = 0 := by rw [map_sub, he, sub_self]
      exact not_isUnit_zero (hz ▸ hu.map e)
    rw [hgen] at hm
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
    choose p hp using fun i => ih (c i)
    refine ⟨MvPolynomial.C (e a) + ∑ i, p i * MvPolynomial.X i, ?_⟩
    have herr : a - P (MvPolynomial.C (e a) + ∑ i, p i * MvPolynomial.X i) =
        ∑ i, (c i - P (p i)) * P (MvPolynomial.X i) := by
      simp only [map_add, map_sum, map_mul]
      rw [sub_add_eq_sub_sub, ← hc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_mul _ _ _).symm
    rw [herr, pow_succ]
    exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_mul (hp i)
      (hgen ▸ Ideal.mem_span_range_self (x := i))

end HodgeLean.Foundations.Program
