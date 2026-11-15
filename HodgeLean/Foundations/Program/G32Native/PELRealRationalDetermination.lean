import HodgeLean.Foundations.Program.G32Native.PELRealPolynomialDetermination

noncomputable section
open MvPolynomial Filter
namespace HodgeLean.Foundations

/-- Polynomial equations on a rational parametrization extend from a real
neighborhood to every complex parameter where its denominator is nonzero. -/
theorem pel_rational_equation_of_real_nhds {ι σ : Type*} [Fintype ι]
    (D : MvPolynomial ι ℂ) (Q : σ → MvPolynomial ι ℂ)
    (φ : (ι → ℂ) → σ → ℂ)
    (hQ : ∀ z, eval z D ≠ 0 → ∀ i, eval z (Q i) = eval z D * φ z i)
    (p : MvPolynomial σ ℂ) (a : ι → ℝ)
    (hD : ∀ᶠ t in nhds a, eval (fun i => (t i : ℂ)) D ≠ 0)
    (hp : ∀ᶠ t in nhds a, eval (φ (fun i => (t i : ℂ))) p = 0) :
    ∀ z, eval z D ≠ 0 → eval (φ z) p = 0 := by
  let U := {z : ι → ℂ // eval z D ≠ 0}
  obtain ⟨F, m, hF⟩ := pel_clear_denominator_substitution
    (fun z : U => z.val) (fun z : U => φ z.val) D Q
    (fun z => hQ z.val z.property) p
  have hzero : F = 0 := by
    apply pel_polynomial_eq_zero_of_real_nhds F a
    filter_upwards [hD, hp] with t ht hpt
    rw [hF ⟨(fun i => (t i : ℂ)), ht⟩, hpt, mul_zero]
  intro z hz
  have hh := hF ⟨z, hz⟩
  rw [hzero, map_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero m hz)

end HodgeLean.Foundations
