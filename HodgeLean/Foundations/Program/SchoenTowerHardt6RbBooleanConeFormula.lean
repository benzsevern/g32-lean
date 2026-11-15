import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools
import Mathlib.Tactic.Linarith

/-! Boolean descriptions of actual radial segments over arbitrary Boolean carriers. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boolean_cone_formula {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (F : s2v_t11b_Formula n) :
    ∃ R : s2v_t11b_Formula n, ∀ z, z ∈ R.realize ↔
      ∃ x ∈ F.realize, ∃ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ i, z i = (1 - t) * a i + t * x i := by
  let u := s2v_hardt2_boundIndex n (n + 1)
  let v := s2v_hardt2_freeIndex n (n + 1)
  let T : MvPolynomial (Fin (n + (n + 1))) ℝ := .X (u 0)
  let P : Fin n → MvPolynomial (Fin (n + (n + 1))) ℝ := fun i =>
    .X (v i) - ((1 - T) * .C (a i) + T * .X (u i.succ))
  obtain ⟨E, hE⟩ := s2v_hardt_cad3_finite_inter (fun i => s2v_t11b_zeroFormula (P i))
  let B := s2v_hardt1_rename (fun i => u i.succ) F
  let W : s2v_t11b_Formula (n + (n + 1)) :=
    B.inter ((s2v_t11b_Formula.nonneg T).inter ((s2v_t11b_Formula.nonneg (1 - T)).inter E))
  have hW : ∀ z, z ∈ W.realize ↔
      WithLp.toLp 2 (fun i => z (u i.succ)) ∈ F.realize ∧
      z (u 0) ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ i, z (v i) = (1 - z (u 0)) * a i + z (u 0) * z (u i.succ) := by
    intro z
    change (z ∈ B.realize ∧ 0 ≤ MvPolynomial.eval (fun i => z i) T ∧
      0 ≤ MvPolynomial.eval (fun i => z i) (1 - T) ∧ z ∈ E.realize) ↔ _
    rw [s2v_hardt1_realize_rename, hE]
    simp only [s2v_t11b_realize_zeroFormula, P, T, map_sub, map_add, map_mul, map_one,
      MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero, sub_nonneg, Set.mem_Icc]
    simp only [and_assoc]
  obtain ⟨R, hR⟩ := s2v_hardt2_repeated_projection W
  refine ⟨R, ?_⟩
  intro z
  rw [hR]
  constructor
  · rintro ⟨w, hw⟩
    have hh := (hW _).mp hw
    simp only [u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free] at hh
    exact ⟨WithLp.toLp 2 (fun i => w i.succ), hh.1, w 0, hh.2.1, hh.2.2⟩
  · rintro ⟨x, hx, t, ht, he⟩
    refine ⟨Fin.cons t (fun i => x i), (hW _).mpr ?_⟩
    simp only [u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free, Fin.cons_succ, Fin.cons_zero]
    exact ⟨hx, ht, he⟩

end HodgeLean.Foundations.Program
