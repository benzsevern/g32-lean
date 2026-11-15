import HodgeLean.Foundations.Program.SchoenTowerT11bSquarefreeQuotient

/-! Polynomial representatives with simple real roots on finite Boolean parameter covers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every polynomial family has a finite Boolean cover carrying polynomial representatives with the same real roots, simple on every nonzero fiber.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite multiplicity removal step. -/
theorem s2v_t11b_finite_squarefree_representatives {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      ∃ H : Fin m → Polynomial (MvPolynomial (Fin n) ℝ),
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ (c i).realize) ∧
      ∀ i t, t ∈ (c i).realize →
        ((H i).map (MvPolynomial.eval (fun j => t j)) = 0 ↔ P.map (MvPolynomial.eval (fun j => t j)) = 0) ∧
        (∀ x : ℝ, (H i).eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 ↔
          P.eval₂ (MvPolynomial.eval (fun j => t j)) x = 0) ∧
        (P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 → ∀ x : ℝ,
          (H i).eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 →
          ((H i).map (MvPolynomial.eval (fun j => t j))).derivative.eval x ≠ 0) := by
  classical
  obtain ⟨m, c, G, hcover, hdiv⟩ := s2v_t11b_finite_gcd_representatives P P.derivative
  have hpieces : ∀ i : Fin m, ∀ tag : Option (Fin ((G i).natDegree + 1)),
      ∃ H : Polynomial (MvPolynomial (Fin n) ℝ),
      ∀ t, t ∈ (c i).realize → t ∈ (s2v_t11b_degreeFormula (G i) tag).realize →
        (H.map (MvPolynomial.eval (fun j => t j)) = 0 ↔ P.map (MvPolynomial.eval (fun j => t j)) = 0) ∧
        (∀ x : ℝ, H.eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 ↔
          P.eval₂ (MvPolynomial.eval (fun j => t j)) x = 0) ∧
        (P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 → ∀ x : ℝ,
          H.eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 →
          (H.map (MvPolynomial.eval (fun j => t j))).derivative.eval x ≠ 0) := by
    intro i tag
    cases tag with
    | none =>
      refine ⟨0, ?_⟩
      intro t ht hd
      have hg := (s2v_t11b_degreeFormula_none (G i) t).mp hd
      have hp : P.map (MvPolynomial.eval (fun j => t j)) = 0 :=
        zero_dvd_iff.mp ((hdiv i t ht 0).mp (by rw [hg])).1
      simp only [Polynomial.map_zero, hp, Polynomial.eval₂_eq_eval_map, Polynomial.eval_zero,
        ne_eq, not_true_eq_false, false_implies, implies_true, and_self]
    | some d =>
      by_cases hc : (G i).coeff d.val = 0
      · refine ⟨0, ?_⟩
        intro t ht hd
        obtain ⟨hn, he⟩ := (s2v_t11b_degreeFormula_some (G i) d t).mp hd
        have hl := Polynomial.leadingCoeff_ne_zero.mpr hn
        rw [Polynomial.leadingCoeff, he, Polynomial.coeff_map, hc, map_zero] at hl
        exact (hl rfl).elim
      · let T := s2v_t11b_degreeTruncation (G i) d.val
        have htl : T.leadingCoeff = (G i).coeff d.val :=
          (s2v_t11b_degreeTruncation_degree (G i) d.val hc).2
        have hT : T ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (htl ▸ hc)
        obtain ⟨k, S, R, he, hr⟩ := s2v_t11b_pseudoDivision_exists P T hT
        refine ⟨S, ?_⟩
        intro t ht hd
        let φ := MvPolynomial.eval (fun j => t j)
        obtain ⟨hgn, hgd⟩ := (s2v_t11b_degreeFormula_some (G i) d t).mp hd
        have hmap : T.map φ = (G i).map φ := s2v_t11b_degreeTruncation_specialize (G i) φ d.val hgd.le
        have hl : φ T.leadingCoeff ≠ 0 := by
          rw [htl]
          have hz := Polynomial.leadingCoeff_ne_zero.mpr hgn
          rwa [Polynomial.leadingCoeff, hgd, Polynomial.coeff_map] at hz
        have hgdiv : ∀ D : Polynomial ℝ, D ∣ T.map φ ↔ D ∣ P.map φ ∧ D ∣ (P.map φ).derivative := by
          intro D
          rw [hmap, Polynomial.derivative_map]
          exact hdiv i t ht D
        have hp : P.map φ ≠ 0 := by
          intro hz
          have hzero : (0 : Polynomial ℝ) ∣ T.map φ := (hgdiv 0).mpr (by simp [hz])
          exact hgn (hmap ▸ zero_dvd_iff.mp hzero)
        have hdvd : T.map φ ∣ P.map φ := ((hgdiv (T.map φ)).mp dvd_rfl).1
        have hR := s2v_t11b_pseudoDivision_remainder_zero P T S R k he hr φ hl hdvd
        have hv := congrArg (Polynomial.map φ) he
        simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_add,
          map_pow, hR, add_zero] at hv
        have hes : T.map φ * S.map φ = Polynomial.C (φ T.leadingCoeff ^ k) * P.map φ := by
          simpa only [Polynomial.C_pow] using hv.symm
        have hu : φ T.leadingCoeff ^ k ≠ 0 := pow_ne_zero k hl
        have hS : S.map φ ≠ 0 := right_ne_zero_of_mul (show T.map φ * S.map φ ≠ 0 by
          rw [hes]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr hu) hp)
        obtain ⟨hz, hs⟩ := s2v_t11b_scaled_squarefree_quotient (P.map φ) (T.map φ) (S.map φ)
          (φ T.leadingCoeff ^ k) hp hu hes hgdiv
        refine ⟨iff_of_false hS hp, ?_, ?_⟩
        · intro x
          simpa only [Polynomial.eval₂_eq_eval_map] using hz x
        · intro _ x hx
          exact hs x (by simpa only [Polynomial.eval₂_eq_eval_map] using hx)
  choose H hH using hpieces
  let J := (i : Fin m) × Option (Fin ((G i).natDegree + 1))
  let E := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun j => .inter (c (E j).1) (s2v_t11b_degreeFormula (G (E j).1) (E j).2),
    fun j => H (E j).1 (E j).2, ?_, ?_⟩
  · intro t
    obtain ⟨i, hi⟩ := hcover t
    obtain ⟨tag, ht, _⟩ := s2v_t11b_degreeFormula_partition (G i) t
    refine ⟨E.symm ⟨i, tag⟩, ?_⟩
    change t ∈ (c (E (E.symm (⟨i, tag⟩ : J))).1).realize ∧
      t ∈ (s2v_t11b_degreeFormula (G (E (E.symm (⟨i, tag⟩ : J))).1) (E (E.symm (⟨i, tag⟩ : J))).2).realize
    rw [E.apply_symm_apply]
    exact ⟨hi, ht⟩
  · intro j t ht
    exact hH (E j).1 (E j).2 t ht.1 ht.2

end HodgeLean.Foundations.Program
