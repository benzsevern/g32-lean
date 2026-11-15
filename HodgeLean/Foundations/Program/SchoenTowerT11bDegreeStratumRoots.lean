import HodgeLean.Foundations.Program.SchoenTowerT11bEffectiveDegree

/-! Ordered actual roots on degree strata, including strata below the original degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Constant actual degree and simple fibers give continuous ordered roots even on a degree-drop stratum.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, effective degree root continuation step. -/
theorem s2v_t11b_degree_stratum_ordered_roots {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) (a : K)
    (hdegree : ∀ t ∈ K, P.map (MvPolynomial.eval (fun i => t i)) ≠ 0 ∧
      (P.map (MvPolynomial.eval (fun i => t i))).natDegree = d)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      (P.map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0) :
    ∃ m : ℕ, ∃ ψ : Fin m → K → ℝ,
      (∀ i, Continuous (ψ i)) ∧ (∀ t, StrictMono (fun i => ψ i t)) ∧
      ∀ t : K, ∀ x : ℝ, P.eval₂ (MvPolynomial.eval (fun i => t.val i)) x = 0 ↔ ∃ i, x = ψ i t := by
  let R := s2v_t11b_degreeTruncation P d
  have hcoeff : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) (P.coeff d) ≠ 0 := by
    intro t ht
    obtain ⟨hn, hd⟩ := hdegree t ht
    have hl := Polynomial.leadingCoeff_ne_zero.mpr hn
    rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_map] at hl
    exact hl
  have hd : P.coeff d ≠ 0 := by
    intro h
    exact hcoeff a.val a.property (by rw [h, map_zero])
  have hmap : ∀ t ∈ K, R.map (MvPolynomial.eval (fun i => t i)) = P.map (MvPolynomial.eval (fun i => t i)) :=
    fun t ht => s2v_t11b_degreeTruncation_specialize P _ d (le_of_eq (hdegree t ht).2)
  have hl : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) R.leadingCoeff ≠ 0 := by
    intro t ht
    rw [(s2v_t11b_degreeTruncation_degree P d hd).2]
    exact hcoeff t ht
  have hs : ∀ t ∈ K, ∀ x : ℝ, R.eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      (R.map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0 := by
    intro t ht x hx
    rw [hmap t ht]
    apply hsimple t ht x
    simpa only [Polynomial.eval₂_eq_eval_map, hmap t ht] using hx
  obtain ⟨m, ψ, hc, hm, hr⟩ := s2v_t11b_mv_parameter_ordered_sections R K hK a hl hs
  refine ⟨m, ψ, hc, hm, ?_⟩
  intro t x
  simpa only [Polynomial.eval₂_eq_eval_map, hmap t.val t.property] using hr t x

end HodgeLean.Foundations.Program
