import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteSimpleDegreePieces

/-! Active polynomial atoms on finite Boolean parameter pieces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Describe a specified pattern of nonzero specialized atom polynomials.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, active atom selection step. -/
def s2v_t11b_activeAtomFormula {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin k → Bool) : s2v_t11b_Formula n :=
  s2v_t11b_refinementFormula (fun i => .compl (s2v_t11b_degreeFormula (Q i) none)) s


/-- The active atom formula records exactly which specialized polynomials are nonzero.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, active atom verification step. -/
theorem s2v_t11b_activeAtomFormula_realize {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin k → Bool)
    (t : EuclideanSpace ℝ (Fin n)) :
    t ∈ (s2v_t11b_activeAtomFormula Q s).realize ↔
      ∀ i, s i = true ↔ (Q i).map (MvPolynomial.eval (fun j => t j)) ≠ 0 := by
  simp only [s2v_t11b_activeAtomFormula, s2v_t11b_realize_refinementFormula,
    s2v_t11b_Formula.realize, Set.mem_compl_iff, s2v_t11b_degreeFormula_none]


/-- Every parameter has exactly one active atom pattern.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite active atom partition step. -/
theorem s2v_t11b_activeAtomFormula_partition {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (t : EuclideanSpace ℝ (Fin n)) :
    ∃! s : Fin k → Bool, t ∈ (s2v_t11b_activeAtomFormula Q s).realize :=
  s2v_t11b_refinement_partition (fun i => .compl (s2v_t11b_degreeFormula (Q i) none)) t


/-- Form the carrier from exactly the selected active polynomial atoms.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, active carrier construction step. -/
def s2v_t11b_activeCarrier {A : Type*} [CommRing A] {k : ℕ}
    (Q : Fin k → Polynomial A) (s : Fin k → Bool) : Polynomial A :=
  ∏ i ∈ Finset.univ.filter (fun i => s i = true), Q i


/-- The active carrier has a nonzero specialized polynomial throughout its active-pattern piece.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, nonvanishing active carrier step. -/
theorem s2v_t11b_activeCarrier_specialize_ne_zero {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin k → Bool)
    (t : EuclideanSpace ℝ (Fin n)) (ht : t ∈ (s2v_t11b_activeAtomFormula Q s).realize) :
    (s2v_t11b_activeCarrier Q s).map (MvPolynomial.eval (fun j => t j)) ≠ 0 := by
  rw [s2v_t11b_activeCarrier, Polynomial.map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ((s2v_t11b_activeAtomFormula_realize Q s t).mp ht i).mp (Finset.mem_filter.mp hi).2


/-- The active carrier roots are exactly the union of the selected atoms' actual roots.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, active carrier root verification step. -/
theorem s2v_t11b_activeCarrier_zero_iff {A : Type*} [CommRing A] {k : ℕ}
    (Q : Fin k → Polynomial A) (s : Fin k → Bool) (φ : A →+* ℝ) (x : ℝ) :
    (s2v_t11b_activeCarrier Q s).eval₂ φ x = 0 ↔
      ∃ i, s i = true ∧ (Q i).eval₂ φ x = 0 := by
  simp only [s2v_t11b_activeCarrier, Polynomial.eval₂_finsetProd, Finset.prod_eq_zero_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]


/-- Collect the active carrier together with each active atom in one finite polynomial family.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, simultaneous active family step. -/
def s2v_t11b_activeFamily {A : Type*} [CommRing A] {k : ℕ}
    (Q : Fin k → Polynomial A) (s : Fin k → Bool) :
    Option {i : Fin k // s i = true} → Polynomial A
  | none => s2v_t11b_activeCarrier Q s
  | some i => Q i.val

end HodgeLean.Foundations.Program
