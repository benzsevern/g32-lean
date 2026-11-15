import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools
import Mathlib.Tactic.Linarith

/-! Polynomial Boolean constraints for an actual finite convex combination. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_barycentric_relation_formula {n m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin n)) :
    ∃ F : s2v_t11b_Formula (n + m), ∀ z,
      z ∈ F.realize ↔
        (∀ j, 0 ≤ z (s2v_hardt2_boundIndex n m j)) ∧
        (∑ j, z (s2v_hardt2_boundIndex n m j)) = 1 ∧
        (∀ i, z (s2v_hardt2_freeIndex n m i) =
          ∑ j, z (s2v_hardt2_boundIndex n m j) * v j i) := by
  classical
  let W : Fin m → MvPolynomial (Fin (n + m)) ℝ :=
    fun j => .X (s2v_hardt2_boundIndex n m j)
  let P : MvPolynomial (Fin (n + m)) ℝ := (∑ j, W j) - 1
  let Q : Fin n → MvPolynomial (Fin (n + m)) ℝ :=
    fun i => .X (s2v_hardt2_freeIndex n m i) - ∑ j, W j * .C (v j i)
  obtain ⟨pos, hpos⟩ := s2v_hardt_cad3_finite_inter (fun j => s2v_t11b_Formula.nonneg (W j))
  obtain ⟨coord, hcoord⟩ := s2v_hardt_cad3_finite_inter
    (fun i => s2v_t11b_Formula.inter (.nonneg (Q i)) (.nonneg (-Q i)))
  let F : s2v_t11b_Formula (n + m) :=
    .inter pos (.inter (.inter (.nonneg P) (.nonneg (-P))) coord)
  refine ⟨F, ?_⟩
  intro z
  change (z ∈ pos.realize ∧
    (0 ≤ MvPolynomial.eval (fun i => z i) P ∧
      0 ≤ MvPolynomial.eval (fun i => z i) (-P)) ∧ z ∈ coord.realize) ↔ _
  rw [hpos, hcoord]
  simp only [s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_setOf_eq,
    W, P, Q, map_sub, map_neg, map_sum, map_one, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  constructor
  · rintro ⟨hpos, ⟨hlo, hup⟩, hcoord⟩
    refine ⟨hpos, by linarith, ?_⟩
    intro i
    have hi := hcoord i
    linarith
  · rintro ⟨hpos, hsum, hcoord⟩
    refine ⟨hpos, ⟨by linarith, by linarith⟩, ?_⟩
    intro i
    rw [hcoord i]
    exact ⟨by simp, by simp⟩

end HodgeLean.Foundations.Program
