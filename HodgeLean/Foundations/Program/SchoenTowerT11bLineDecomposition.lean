import HodgeLean.Foundations.Program.SchoenTowerT11bIntervals
import HodgeLean.Foundations.Program.SchoenTowerT11bRefinement
import Mathlib.Data.Fintype.EquivFin

/-! Finite exceptional values for polynomial Boolean sets on the real line.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Collect the real roots of the nonconstant tests along the diagonal.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
def s2v_t11b_Formula.exceptionalValues {n : ℕ} : s2v_t11b_Formula n → Finset ℝ
  | .nonneg p =>
    (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) p).roots.toFinset
  | .compl f => f.exceptionalValues
  | .inter f g => f.exceptionalValues ∪ g.exceptionalValues

/-- Outside the finite root set, every nonzero polynomial has constant sign on a connected set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_polynomial_sign_off_roots (p : Polynomial ℝ)
    (S : Set ℝ) (hS : IsPreconnected S)
    (havoid : ∀ t ∈ S, t ∉ p.roots.toFinset)
    (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) :
    0 ≤ p.eval a ↔ 0 ≤ p.eval b := by
  by_cases hp : p = 0
  · subst p
    simp only [Polynomial.eval_zero]
  · apply s2v_t11b_nonzero_sign S hS (fun t => p.eval t) p.continuous.continuousOn
      (fun t ht hzero => havoid t ht ?_) a b ha hb
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hzero)

/-- A Boolean polynomial test is constant on every connected set avoiding its exceptional values.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_formula_constant_off_exceptionalValues {n : ℕ}
    (f : s2v_t11b_Formula n) (S : Set ℝ) (hS : IsPreconnected S)
    (havoid : ∀ t ∈ S, t ∉ f.exceptionalValues)
    (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) :
    WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize ↔
      WithLp.toLp 2 (fun _ : Fin n => b) ∈ f.realize := by
  induction f with
  | nonneg p =>
    simpa only [s2v_t11b_Formula.realize, Set.mem_ofPred_eq, s2v_t11b_eval_diagonal]
      using s2v_t11b_polynomial_sign_off_roots
        (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) p)
        S hS havoid a b ha hb
  | compl f ih => exact not_congr (ih havoid)
  | inter f g ihf ihg =>
    exact and_congr
      (ihf (fun t ht hmem => havoid t ht (Finset.mem_union_left _ hmem)))
      (ihg (fun t ht hmem => havoid t ht (Finset.mem_union_right _ hmem)))

/-- Comparisons with the finite exceptional values determine the Boolean membership.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_formula_constant_on_root_cuts {n : ℕ}
    (f : s2v_t11b_Formula n) (a b : ℝ)
    (hcuts : ∀ r ∈ f.exceptionalValues,
      (a ≤ r ↔ b ≤ r) ∧ (r ≤ a ↔ r ≤ b)) :
    WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize ↔
      WithLp.toLp 2 (fun _ : Fin n => b) ∈ f.realize := by
  by_cases hab : a = b
  · subst b
    rfl
  · apply s2v_t11b_formula_constant_off_exceptionalValues f (Set.uIcc a b)
      isPreconnected_uIcc ?_ a b Set.left_mem_uIcc Set.right_mem_uIcc
    intro r hr hmem
    obtain ⟨hl, hu⟩ := hcuts r hmem
    apply hab
    rcases Set.mem_uIcc.mp hr with hr | hr
    · have hbr := hl.mp hr.1
      have hra := hu.mpr hr.2
      exact le_antisymm (hr.1.trans hr.2) (hbr.trans hra)
    · have har := hl.mpr hr.1
      have hrb := hu.mp hr.2
      exact le_antisymm (har.trans hrb) (hr.1.trans hr.2)

/-- Two linear tests per cut distinguish both sides and the cut point itself.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
def s2v_t11b_rootCutTests {k : ℕ} (d : Fin k → ℝ) :
    Fin (k + k) → s2v_t11b_Formula 1 :=
  Fin.addCases
    (fun i => .nonneg (MvPolynomial.X 0 - MvPolynomial.C (d i)))
    (fun i => .nonneg (-(MvPolynomial.X 0 - MvPolynomial.C (d i))))

/-- The first linear test compares the base value from below.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_rootCutTests_lower {k : ℕ} (d : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_rootCutTests d (i.castAdd k)).realize ↔ d i ≤ t := by
  simp only [s2v_t11b_rootCutTests, Fin.addCases_left, s2v_t11b_Formula.realize,
    Set.mem_ofPred_eq, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg]

/-- The second linear test compares the base value from above.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_rootCutTests_upper {k : ℕ} (d : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_rootCutTests d (Fin.natAdd k i)).realize ↔ t ≤ d i := by
  simp only [s2v_t11b_rootCutTests, Fin.addCases_right, s2v_t11b_Formula.realize,
    Set.mem_ofPred_eq, map_neg, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    neg_nonneg, sub_nonpos]

/-- Construct a finite Boolean polynomial partition of the line compatible with a given test.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD construction. -/
theorem s2v_t11b_line_partition {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i a b,
        WithLp.toLp 2 (fun _ : Fin 1 => a) ∈ (c i).realize →
        WithLp.toLp 2 (fun _ : Fin 1 => b) ∈ (c i).realize →
        (WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize ↔
          WithLp.toLp 2 (fun _ : Fin n => b) ∈ f.realize) := by
  classical
  let R := {r : ℝ // r ∈ f.exceptionalValues}
  let k := Fintype.card R
  let E : Fin k ≃ R := (Fintype.equivFin R).symm
  let d : Fin k → ℝ := fun i => (E i).val
  let C := s2v_t11b_rootCutTests d
  let F := (Fintype.equivFin (Fin (k + k) → Bool)).symm
  refine ⟨Fintype.card (Fin (k + k) → Bool), fun i => s2v_t11b_refinementFormula C (F i),
    ?_, ?_⟩
  · intro t
    obtain ⟨s, hs, huniq⟩ := s2v_t11b_refinement_partition C
      (WithLp.toLp 2 (fun _ : Fin 1 => t))
    refine ⟨F.symm s, ?_, ?_⟩
    · simpa only [F.apply_symm_apply] using hs
    · intro j hj
      apply F.injective
      simpa only [F.apply_symm_apply] using huniq (F j) hj
  · intro i a b ha hb
    have hsame : ∀ j, WithLp.toLp 2 (fun _ : Fin 1 => a) ∈ (C j).realize ↔
        WithLp.toLp 2 (fun _ : Fin 1 => b) ∈ (C j).realize := fun j =>
      ((s2v_t11b_realize_refinementFormula C (F i) _).mp ha j).symm.trans
        ((s2v_t11b_realize_refinementFormula C (F i) _).mp hb j)
    apply s2v_t11b_formula_constant_on_root_cuts f a b
    intro r hr
    let j := E.symm ⟨r, hr⟩
    have hd : d j = r := congrArg Subtype.val (E.apply_symm_apply ⟨r, hr⟩)
    constructor
    · simpa only [C, s2v_t11b_rootCutTests_upper, hd] using hsame (Fin.natAdd k j)
    · simpa only [C, s2v_t11b_rootCutTests_lower, hd] using hsame (j.castAdd k)

end HodgeLean.Foundations.Program
