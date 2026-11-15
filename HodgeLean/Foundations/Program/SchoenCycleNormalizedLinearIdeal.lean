import HodgeLean.Foundations.Program.SchoenCycleNormalizedPolynomialQuotient
import HodgeLean.Foundations.Program.SchoenCycleLinearPolynomialRadical

/-! # Reduced linear equations in normalized projective chart rings -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The homogeneous linear equation in the actual normalized polynomial quotient has a radical principal ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_normalized_linear_span_isRadical {σ : Type*} [Fintype σ]
    (i : σ) (a : σ → ℂ) :
    (Ideal.span ({(Ideal.Quotient.mk
      (Ideal.span ({X i - 1} : Set (MvPolynomial σ ℂ)))
      (∑ j, C (a j) * X j))} : Set
        (MvPolynomial σ ℂ ⧸ Ideal.span ({X i - 1} : Set (MvPolynomial σ ℂ))))).IsRadical := by
  classical
  let e := s2e_normalizedPolynomialQuotientEquiv (R := ℂ) i
  let F := Ideal.Quotient.mk (Ideal.span ({X i - 1} : Set (MvPolynomial σ ℂ)))
    (∑ j, C (a j) * X j)
  let J := Ideal.span ({F} : Set (MvPolynomial σ ℂ ⧸ Ideal.span ({X i - 1} : Set (MvPolynomial σ ℂ))))
  have he : (J.map e.toRingHom).IsRadical := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    apply s2e_linear_polynomial_span_isRadical
    change (e F).totalDegree ≤ 1
    dsimp only [e, F]
    rw [s2e_normalizedPolynomialQuotientEquiv_mk]
    simp only [map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']
    apply totalDegree_finsetSum_le
    intro j hj
    by_cases h : j = i
    · simp [h]
    · simp only [dif_neg h]
      exact (totalDegree_mul _ _).trans (by simp)
  have hc := he.comap e.toRingHom
  rw [J.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

end HodgeLean.Foundations.Program
