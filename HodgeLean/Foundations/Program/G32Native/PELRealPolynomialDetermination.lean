import HodgeLean.Foundations.Program.G32Native.PELZariskiRationalMaps

noncomputable section
open MvPolynomial Set
namespace HodgeLean.Foundations

/-- A complex polynomial vanishing on a real open neighborhood is zero. -/
theorem pel_polynomial_eq_zero_of_real_nhds {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℂ) (a : ι → ℝ)
    (hp : ∀ᶠ x in nhds a, eval (fun i => (x i : ℂ)) p = 0) : p = 0 := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hp
  let s : ι → Set ℂ := fun i => Complex.ofReal '' Ioo (a i - ε) (a i + ε)
  apply MvPolynomial.funext_set s (fun i => ?_) (fun z hz => ?_)
  · apply (Set.Ioo_infinite (by linarith : a i - ε < a i + ε)).image
    exact Complex.ofReal_injective.injOn
  · have hz' : ∀ i, ∃ t : ℝ, t ∈ Ioo (a i - ε) (a i + ε) ∧ (t : ℂ) = z i :=
      fun i => hz i (mem_univ i)
    choose x hx hxe using hz'
    have hxa : x ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      rw [Real.dist_eq, abs_lt]
      constructor <;> have hi := hx i <;> linarith [hi.1, hi.2]
    have he : z = fun i => (x i : ℂ) := by funext i; exact (hxe i).symm
    rw [he, hball hxa, map_zero]

end HodgeLean.Foundations
