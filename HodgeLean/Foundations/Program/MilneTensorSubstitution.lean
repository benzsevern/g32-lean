import HodgeLean.Foundations.Program.MilneTensorDescent

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_polynomial_pivot_denominator {A R S σ : Type*}
    [CommRing A] [CommRing R] [CommRing S] (f : A →+* R) (g : R →+* S)
    (a : R) (v : σ → S)
    (hv : ∀ i, ∃ k : ℕ, ∃ b : R, g a ^ k * v i = g b)
    (p : MvPolynomial σ A) :
    ∃ k : ℕ, ∃ b : R, g a ^ k * MvPolynomial.eval₂Hom (g.comp f) v p = g b := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, f c, ?_⟩
    simp only [pow_zero, one_mul, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  | add p q hp hq =>
    obtain ⟨m, b, hb⟩ := hp
    obtain ⟨n, c, hc⟩ := hq
    refine ⟨m + n, a ^ n * b + a ^ m * c, ?_⟩
    rw [map_add]
    calc
      g a ^ (m + n) * (MvPolynomial.eval₂Hom (g.comp f) v p +
          MvPolynomial.eval₂Hom (g.comp f) v q) =
          g a ^ n * (g a ^ m * MvPolynomial.eval₂Hom (g.comp f) v p) +
          g a ^ m * (g a ^ n * MvPolynomial.eval₂Hom (g.comp f) v q) := by
        rw [pow_add]
        ring
      _ = g (a ^ n * b + a ^ m * c) := by rw [hb, hc, map_add, map_mul, map_mul, map_pow, map_pow]
  | mul_X p i hp =>
    obtain ⟨m, b, hb⟩ := hp
    obtain ⟨n, c, hc⟩ := hv i
    refine ⟨m + n, b * c, ?_⟩
    rw [map_mul, MvPolynomial.eval₂Hom_X']
    calc
      g a ^ (m + n) * (MvPolynomial.eval₂Hom (g.comp f) v p * v i) =
          (g a ^ m * MvPolynomial.eval₂Hom (g.comp f) v p) * (g a ^ n * v i) := by
        rw [pow_add]
        ring
      _ = g (b * c) := by rw [hb, hc, map_mul]

end HodgeLean.Foundations.Program
