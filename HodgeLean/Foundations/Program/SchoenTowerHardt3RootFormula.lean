import HodgeLean.Foundations.Program.SchoenTowerHardt2Coordinates
import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalEncoding

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The union of the actual roots of nonzero specializations has a Boolean description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, active-root equation. -/
theorem s2v_hardt3_active_root_formula {n k : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ f : s2v_t11b_Formula (n + 1), ∀ a : EuclideanSpace ℝ (Fin n), ∀ x : ℝ,
      WithLp.toLp 2 (Fin.cons x (fun j => a j)) ∈ f.realize ↔
      ∃ j, (P j).map (MvPolynomial.eval (fun v => a v)) ≠ 0 ∧
        (P j).eval₂ (MvPolynomial.eval (fun v => a v)) x = 0 := by
  let Q := fun j => (MvPolynomial.finSuccEquiv ℝ n).symm (P j)
  let F := fun j => s2v_t11b_Formula.inter
    (s2v_hardt1_rename Fin.succ (.compl (s2v_t11b_degreeFormula (P j) none)))
    (.inter (.nonneg (Q j)) (.nonneg (-Q j)))
  obtain ⟨f, hf⟩ := s2v_t11b_finite_union_formula F
  refine ⟨f, ?_⟩
  intro a x
  rw [hf]
  apply exists_congr
  intro j
  change (_ ∈ (s2v_hardt1_rename Fin.succ _).realize ∧ _) ↔ _
  rw [s2v_hardt1_realize_rename]
  have he : MvPolynomial.eval (Fin.cons x (fun i => a i)) (Q j) =
      (P j).eval₂ (MvPolynomial.eval (fun i => a i)) x := by
    rw [← s2v_t11b_finSucc_family_eval]
    simp only [Q, AlgEquiv.apply_symm_apply]
  simp only [s2v_t11b_Formula.realize, Set.mem_compl_iff,
    s2v_t11b_degreeFormula_none, Set.mem_inter_iff, Set.mem_setOf_eq, map_neg,
    WithLp.ofLp_toLp, Fin.cons_succ, he, neg_nonneg]
  exact and_congr_right (fun _ => ⟨fun h => le_antisymm h.2 h.1,
    fun h => by simp [h]⟩)

#print axioms s2v_hardt3_active_root_formula
end HodgeLean.Foundations.Program
