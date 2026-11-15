import HodgeLean.Foundations.Program.SchoenTowerT11bDegreePartition

/-! Actual polynomial representatives on every finite degree stratum.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Retain exactly the coefficients up to a specified spatial degree.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, effective degree representative step. -/
def s2v_t11b_degreeTruncation {A : Type*} [Semiring A] (P : Polynomial A) (d : ℕ) : Polynomial A :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.monomial j (P.coeff j)


/-- The effective degree representative retains every lower coefficient and has no higher coefficients.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, effective coefficient verification step. -/
theorem s2v_t11b_degreeTruncation_coeff {A : Type*} [Semiring A]
    (P : Polynomial A) (d j : ℕ) :
    (s2v_t11b_degreeTruncation P d).coeff j = if j ≤ d then P.coeff j else 0 := by
  simp [s2v_t11b_degreeTruncation, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Nat.lt_succ_iff]


/-- Truncation retains the entire actual specialized polynomial whenever its degree lies below the cutoff.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, effective specialization step. -/
theorem s2v_t11b_degreeTruncation_specialize {A B : Type*} [Semiring A] [Semiring B]
    (P : Polynomial A) (φ : A →+* B) (d : ℕ) (hd : (P.map φ).natDegree ≤ d) :
    (s2v_t11b_degreeTruncation P d).map φ = P.map φ := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, s2v_t11b_degreeTruncation_coeff]
  by_cases hj : j ≤ d
  · rw [if_pos hj, Polynomial.coeff_map]
  · rw [if_neg hj, map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (Nat.lt_of_not_ge hj))).symm


/-- A nonzero cutoff coefficient becomes the exact leading coefficient of the effective representative.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, effective leading coefficient step. -/
theorem s2v_t11b_degreeTruncation_degree {A : Type*} [Semiring A]
    (P : Polynomial A) (d : ℕ) (hd : P.coeff d ≠ 0) :
    (s2v_t11b_degreeTruncation P d).natDegree = d ∧
      (s2v_t11b_degreeTruncation P d).leadingCoeff = P.coeff d := by
  have hdeg : (s2v_t11b_degreeTruncation P d).natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      rw [s2v_t11b_degreeTruncation_coeff, if_neg (not_le_of_gt hj)]
    · simpa only [s2v_t11b_degreeTruncation_coeff, if_pos (le_refl d)] using hd
  refine ⟨hdeg, ?_⟩
  rw [Polynomial.leadingCoeff, hdeg, s2v_t11b_degreeTruncation_coeff, if_pos (le_refl d)]

end HodgeLean.Foundations.Program
