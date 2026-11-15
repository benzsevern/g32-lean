import HodgeLean.Foundations.Program.SchoenTowerT11bPseudoDivision

/-! Finite Boolean parameter covers carrying actual polynomial gcd representatives.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every polynomial pair has a finite Boolean parameter cover with polynomial representatives of all specialized common divisors.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite polynomial remainder decomposition step. -/
theorem s2v_t11b_finite_gcd_representatives {n : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      ∃ G : Fin m → Polynomial (MvPolynomial (Fin n) ℝ),
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ (c i).realize) ∧
      ∀ i t, t ∈ (c i).realize → ∀ D : Polynomial ℝ,
        (D ∣ (G i).map (MvPolynomial.eval (fun j => t j)) ↔
          D ∣ P.map (MvPolynomial.eval (fun j => t j)) ∧
          D ∣ Q.map (MvPolynomial.eval (fun j => t j))) := by
  classical
  by_cases hQ : Q = 0
  · refine ⟨1, fun _ => .nonneg 0, fun _ => P, ?_, ?_⟩
    · intro t
      exact ⟨0, by simp [s2v_t11b_Formula.realize]⟩
    · intro i t ht D
      simp only [hQ, Polynomial.map_zero, dvd_zero, and_true]
  have hpieces : ∀ tag : Option (Fin (Q.natDegree + 1)),
      ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
        ∃ G : Fin m → Polynomial (MvPolynomial (Fin n) ℝ),
        (∀ t, t ∈ (s2v_t11b_degreeFormula Q tag).realize → ∃ i, t ∈ (c i).realize) ∧
        ∀ i t, t ∈ (c i).realize → ∀ D : Polynomial ℝ,
          (D ∣ (G i).map (MvPolynomial.eval (fun j => t j)) ↔
            D ∣ P.map (MvPolynomial.eval (fun j => t j)) ∧
            D ∣ Q.map (MvPolynomial.eval (fun j => t j))) := by
    intro tag
    cases tag with
    | none =>
      refine ⟨1, fun _ => s2v_t11b_degreeFormula Q none, fun _ => P,
        fun t ht => ⟨0, ht⟩, ?_⟩
      intro i t ht D
      rw [(s2v_t11b_degreeFormula_none Q t).mp ht]
      simp only [dvd_zero, and_true]
    | some d =>
      by_cases hc : Q.coeff d.val = 0
      · refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun i => Fin.elim0 i⟩
        intro t ht
        obtain ⟨hn, hd⟩ := (s2v_t11b_degreeFormula_some Q d t).mp ht
        have hl := Polynomial.leadingCoeff_ne_zero.mpr hn
        rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_map, hc, map_zero] at hl
        exact (hl rfl).elim
      · let T := s2v_t11b_degreeTruncation Q d.val
        have htd : T.natDegree = d.val := (s2v_t11b_degreeTruncation_degree Q d.val hc).1
        have htl : T.leadingCoeff = Q.coeff d.val := (s2v_t11b_degreeTruncation_degree Q d.val hc).2
        have hT : T ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (htl ▸ hc)
        obtain ⟨k, S, R, he, hr⟩ := s2v_t11b_pseudoDivision_exists P T hT
        have hlt : R.degree < Q.degree := by
          apply hr.trans_le
          rw [Polynomial.degree_eq_natDegree hT, Polynomial.degree_eq_natDegree hQ, htd]
          exact_mod_cast Nat.le_of_lt_succ d.isLt
        obtain ⟨m, c, G, hcover, hdiv⟩ := s2v_t11b_finite_gcd_representatives T R
        refine ⟨m, fun i => .inter (s2v_t11b_degreeFormula Q (some d)) (c i), G, ?_, ?_⟩
        · intro t ht
          obtain ⟨i, hi⟩ := hcover t
          exact ⟨i, ht, hi⟩
        · intro i t ht D
          obtain ⟨hn, hd⟩ := (s2v_t11b_degreeFormula_some Q d t).mp ht.1
          have hmap : T.map (MvPolynomial.eval (fun j => t j)) = Q.map (MvPolynomial.eval (fun j => t j)) :=
            s2v_t11b_degreeTruncation_specialize Q _ d.val hd.le
          have hl : MvPolynomial.eval (fun j => t j) T.leadingCoeff ≠ 0 := by
            rw [htl]
            have hz := Polynomial.leadingCoeff_ne_zero.mpr hn
            rwa [Polynomial.leadingCoeff, hd, Polynomial.coeff_map] at hz
          have hstep := s2v_t11b_pseudoDivision_common_divisors P T S R k he
            (MvPolynomial.eval (fun j => t j)) hl D
          rw [hmap] at hstep
          have hg := hdiv i t ht.2 D
          rw [hmap] at hg
          exact hg.trans hstep.symm
  choose m c G hcover hdiv using hpieces
  let J := (tag : Option (Fin (Q.natDegree + 1))) × Fin (m tag)
  let E := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => c (E i).1 (E i).2,
    fun i => G (E i).1 (E i).2, ?_, ?_⟩
  · intro t
    obtain ⟨tag, ht, _⟩ := s2v_t11b_degreeFormula_partition Q t
    obtain ⟨i, hi⟩ := hcover tag t ht
    refine ⟨E.symm ⟨tag, i⟩, ?_⟩
    change t ∈ (c (E (E.symm (⟨tag, i⟩ : J))).1 (E (E.symm (⟨tag, i⟩ : J))).2).realize
    rw [E.apply_symm_apply]
    exact hi
  · intro i t ht D
    exact hdiv (E i).1 (E i).2 t ht D
termination_by Q.degree
decreasing_by exact hlt

end HodgeLean.Foundations.Program
