import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalEncoding
import HodgeLean.Foundations.Program.SchoenTowerT11bRefinement

/-! Finite Boolean parameter partitions by actual specialized spatial degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Encode all zero fibers and every possible nonzero specialized degree by finite coefficient tests.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, degree-stratum construction step. -/
def s2v_t11b_degreeFormula {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Option (Fin (P.natDegree + 1)) → s2v_t11b_Formula n
  | none => s2v_t11b_Formula.conjunction
      ((List.range (P.natDegree + 1)).map (fun j => s2v_t11b_zeroFormula (P.coeff j)))
  | some d => .inter (.compl (s2v_t11b_zeroFormula (P.coeff d.val)))
      (s2v_t11b_Formula.conjunction
        (((List.range (P.natDegree + 1)).filter (fun j => d.val < j)).map
          (fun j => s2v_t11b_zeroFormula (P.coeff j))))


/-- The zero-fiber label describes exactly the parameters whose specialized polynomial is identically zero.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, zero-fiber stratum verification step. -/
theorem s2v_t11b_degreeFormula_none {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (t : EuclideanSpace ℝ (Fin n)) :
    t ∈ (s2v_t11b_degreeFormula P none).realize ↔ P.map (MvPolynomial.eval (fun i => t i)) = 0 := by
  simp only [s2v_t11b_degreeFormula, s2v_t11b_realize_conjunction, List.forall_mem_map,
    List.mem_range, s2v_t11b_realize_zeroFormula]
  constructor
  · intro h
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < P.natDegree + 1
    · exact h j hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < j), map_zero]
  · intro h j _
    have hc := congrArg (fun Q : Polynomial ℝ => Q.coeff j) h
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hc


/-- Every degree label describes exactly the nonzero fibers of the indicated actual spatial degree.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized degree-stratum verification step. -/
theorem s2v_t11b_degreeFormula_some {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (d : Fin (P.natDegree + 1)) (t : EuclideanSpace ℝ (Fin n)) :
    t ∈ (s2v_t11b_degreeFormula P (some d)).realize ↔
      P.map (MvPolynomial.eval (fun i => t i)) ≠ 0 ∧
      (P.map (MvPolynomial.eval (fun i => t i))).natDegree = d.val := by
  simp only [s2v_t11b_degreeFormula, s2v_t11b_Formula.realize, Set.mem_inter_iff,
    Set.mem_compl_iff, s2v_t11b_realize_zeroFormula, s2v_t11b_realize_conjunction,
    List.forall_mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  let Q := P.map (MvPolynomial.eval (fun i => t i))
  constructor
  · rintro ⟨hn, hz⟩
    have hcoeff : Q.coeff d.val ≠ 0 := by simpa only [Q, Polynomial.coeff_map] using hn
    have hQ : Q ≠ 0 := fun h => hcoeff (by rw [h, Polynomial.coeff_zero])
    refine ⟨hQ, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ hcoeff⟩
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [Polynomial.coeff_map]
    by_cases hb : j < P.natDegree + 1
    · exact hz j ⟨hb, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < j), map_zero]
  · rintro ⟨hQ, hd⟩
    have hcoeff : Q.coeff d.val ≠ 0 := by
      rw [← hd]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    refine ⟨by simpa only [Q, Polynomial.coeff_map] using hcoeff, ?_⟩
    intro j hj
    have hdQ : Q.natDegree = d.val := hd
    have he : Q.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdQ]; exact hj.2)
    simpa only [Q, Polynomial.coeff_map] using he


/-- The coefficient formulas form a finite disjoint cover of the entire parameter space, retaining all degree-drop and zero fibers.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite degree partition step. -/
theorem s2v_t11b_degreeFormula_partition {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (t : EuclideanSpace ℝ (Fin n)) :
    ∃! d : Option (Fin (P.natDegree + 1)), t ∈ (s2v_t11b_degreeFormula P d).realize := by
  let Q := P.map (MvPolynomial.eval (fun i => t i))
  by_cases hQ : Q = 0
  · refine ⟨none, (s2v_t11b_degreeFormula_none P t).mpr hQ, ?_⟩
    intro d hd
    cases d with
    | none => rfl
    | some d => exact ((s2v_t11b_degreeFormula_some P d t).mp hd).1 hQ |>.elim
  · let d : Fin (P.natDegree + 1) := ⟨Q.natDegree, Nat.lt_succ_of_le Polynomial.natDegree_map_le⟩
    refine ⟨some d, (s2v_t11b_degreeFormula_some P d t).mpr ⟨hQ, rfl⟩, ?_⟩
    intro e he
    cases e with
    | none => exact (hQ ((s2v_t11b_degreeFormula_none P t).mp he)).elim
    | some e =>
      apply congrArg some
      apply Fin.ext
      exact ((s2v_t11b_degreeFormula_some P e t).mp he).2.symm

end HodgeLean.Foundations.Program
