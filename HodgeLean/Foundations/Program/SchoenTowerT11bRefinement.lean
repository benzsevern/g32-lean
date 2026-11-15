import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Boolean refinement of finite families of polynomial descriptions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite intersections remain concrete Boolean polynomial expressions.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, Boolean refinement step. -/
def s2v_t11b_Formula.conjunction {n : ℕ} : List (s2v_t11b_Formula n) → s2v_t11b_Formula n
  | [] => .nonneg 0
  | f :: fs => .inter f (s2v_t11b_Formula.conjunction fs)

/-- A finite conjunction has exactly the memberships of its entries.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, Boolean refinement step. -/
theorem s2v_t11b_realize_conjunction {n : ℕ} (fs : List (s2v_t11b_Formula n))
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (s2v_t11b_Formula.conjunction fs).realize ↔ ∀ f ∈ fs, x ∈ f.realize := by
  induction fs with
  | nil => simp only [s2v_t11b_Formula.conjunction, s2v_t11b_Formula.realize,
      Set.mem_setOf_eq, map_zero, le_refl, List.not_mem_nil, false_implies, implies_true]
  | cons f fs ih =>
    simp only [s2v_t11b_Formula.conjunction, s2v_t11b_Formula.realize,
      Set.mem_inter_iff, ih, List.mem_cons, forall_eq_or_imp]

/-- Each truth pattern gives an explicit Boolean piece of a finite family.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, Boolean refinement step. -/
def s2v_t11b_refinementFormula {n m : ℕ} (c : Fin m → s2v_t11b_Formula n)
    (s : Fin m → Bool) : s2v_t11b_Formula n :=
  s2v_t11b_Formula.conjunction
    (Finset.univ.toList.map (fun i => if s i then c i else .compl (c i)))

/-- Membership in a truth-pattern piece records each original membership exactly.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, Boolean refinement step. -/
theorem s2v_t11b_realize_refinementFormula {n m : ℕ} (c : Fin m → s2v_t11b_Formula n)
    (s : Fin m → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (s2v_t11b_refinementFormula c s).realize ↔
      ∀ i, s i = true ↔ x ∈ (c i).realize := by
  rw [s2v_t11b_refinementFormula, s2v_t11b_realize_conjunction]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  apply forall_congr'
  intro i
  cases h : s i <;>
    simp only [h, Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      s2v_t11b_Formula.realize, Set.mem_compl_iff, false_iff, true_iff]

/-- Every point belongs to exactly one of the finitely many truth-pattern pieces.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, Boolean refinement step. -/
theorem s2v_t11b_refinement_partition {n m : ℕ} (c : Fin m → s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃! s : Fin m → Bool, x ∈ (s2v_t11b_refinementFormula c s).realize := by
  classical
  refine ⟨fun i => decide (x ∈ (c i).realize), ?_, ?_⟩
  · exact (s2v_t11b_realize_refinementFormula c _ x).mpr (fun _ => decide_eq_true_iff)
  · intro s hs
    funext i
    apply Bool.eq_iff_iff.mpr
    exact ((s2v_t11b_realize_refinementFormula c s x).mp hs i).trans
      decide_eq_true_iff.symm

end HodgeLean.Foundations.Program
