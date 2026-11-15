import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleChartBaseChange
import HodgeLean.Foundations.Program.SchoenTowerL1bChartTensor

/-! Etale coordinates on binomial charts over an etale coordinate algebra.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
universe u
namespace HodgeLean.Foundations.Program

/-- A binomial chart over an etale coordinate algebra again has etale coordinates,
with the actual ground coefficient map and all untouched coordinates retained. -/
theorem s2v_l1b_etale_binomial_chart
    {k R σ : Type u} [CommRing k] [CommRing R] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    (a b : σ) (hab : a ≠ b) :
    let f := algebraMap (MvPolynomial σ k) R
    let Q := s2v_L1bChart (f (MvPolynomial.X a)) (f (MvPolynomial.X b))
    let q := Ideal.Quotient.mk (Ideal.span
      {Polynomial.C (f (MvPolynomial.X a)) - Polynomial.X * Polynomial.C (f (MvPolynomial.X b))})
    ∃ z : σ → Q,
      (MvPolynomial.eval₂Hom ((q.comp Polynomial.C).comp (f.comp MvPolynomial.C)) z).Etale ∧
      (∀ j, q (Polynomial.C (f (MvPolynomial.X j))) =
        if j = a then z a * z b else z j) := by
  dsimp only
  let P := MvPolynomial σ k
  let f := algebraMap P R
  let Q₀ := s2v_L1bChart (MvPolynomial.X a : P) (MvPolynomial.X b)
  let T := Q₀ ⊗[P] R
  let Q := s2v_L1bChart (f (MvPolynomial.X a)) (f (MvPolynomial.X b))
  let q := Ideal.Quotient.mk (Ideal.span
    {Polynomial.C (f (MvPolynomial.X a)) - Polynomial.X * Polynomial.C (f (MvPolynomial.X b))})
  obtain ⟨c, z, het, hc, hz⟩ := s2v_l1b_etale_chart_baseChange (k := k) (R := R) a b hab
  obtain ⟨e, heC, heX⟩ := s2v_l1b_chart_tensor_equiv (A := R)
    (MvPolynomial.X a : P) (MvPolynomial.X b)
  let c' : k →+* Q := (q.comp Polynomial.C).comp (f.comp MvPolynomial.C)
  have hcomp : MvPolynomial.eval₂Hom c' (fun j => e (z j)) =
      e.toRingHom.comp (MvPolynomial.eval₂Hom c z) := by
    apply MvPolynomial.ringHom_ext
    · intro d
      rw [MvPolynomial.eval₂Hom_C]
      change c' d = e ((MvPolynomial.eval₂Hom c z) (MvPolynomial.C d))
      rw [MvPolynomial.eval₂Hom_C]
      rw [hc, heC]
      rfl
    · intro j
      rw [MvPolynomial.eval₂Hom_X']
      change e (z j) = e ((MvPolynomial.eval₂Hom c z) (MvPolynomial.X j))
      rw [MvPolynomial.eval₂Hom_X']
  refine ⟨fun j => e (z j), ?_, ?_⟩
  · change (MvPolynomial.eval₂Hom c' (fun j => e (z j))).Etale
    rw [hcomp]
    exact RingHom.Etale.stableUnderComposition _ _ het
      (RingHom.Etale.of_bijective e.bijective)
  · intro j
    have H := congrArg e (hz j)
    rw [heC] at H
    by_cases hja : j = a
    · rw [ite_eq_left hja, map_mul] at H
      rw [ite_eq_left hja]
      exact H
    · rw [ite_eq_right hja] at H ⊢
      exact H

end HodgeLean.Foundations.Program
