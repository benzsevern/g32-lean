import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionSubstitution

/-! Actual endpoint graphs construct actual Boolean graph cells and strict band cells. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_section_cell_formula {n : ℕ}
    (C : s2v_t11b_Formula n) (l u : C.realize → ℝ)
    (gl gu : s2v_t11b_Formula (n + 1))
    (hgl : ∀ z, z ∈ gl.realize ↔ ∃ x : C.realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = l x)
    (hgu : ∀ z, z ∈ gu.realize ↔ ∃ x : C.realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = u x)
    (graph : Bool) :
    ∃ F : s2v_t11b_Formula (n + 1), ∀ z, z ∈ F.realize ↔
      ∃ x : C.realize, (∀ i, z i.succ = x.val i) ∧
        (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x) := by
  let s : Fin 2 → C.realize → ℝ := Fin.cons l (Fin.cons u Fin.elim0)
  let g : Fin 2 → s2v_t11b_Formula (n + 1) := Fin.cons gl (Fin.cons gu Fin.elim0)
  have hg : ∀ j z, z ∈ (g j).realize ↔ ∃ x : C.realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = s j x := by
    intro j
    refine Fin.cases hgl (fun i => ?_) j
    exact Fin.cases hgu (fun a => Fin.elim0 a) i
  let A : MvPolynomial (Fin ((n + 1) + 2)) ℝ := .X (s2v_hardt2_boundIndex (n + 1) 2 0)
  let B : MvPolynomial (Fin ((n + 1) + 2)) ℝ := .X (s2v_hardt2_boundIndex (n + 1) 2 1)
  let Y : MvPolynomial (Fin ((n + 1) + 2)) ℝ := .X (s2v_hardt2_freeIndex (n + 1) 2 0)
  let R : s2v_t11b_Formula ((n + 1) + 2) := if graph then
    .inter (.nonneg (Y - A)) (.nonneg (A - Y)) else
    .inter (.compl (.nonneg (A - Y))) (.compl (.nonneg (Y - B)))
  have hR (x : C.realize) (z : EuclideanSpace ℝ (Fin (n + 1))) :
      s2v_hardt2_insert 2 (fun j => s j x) z ∈ R.realize ↔
        (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x) := by
    cases graph <;>
      simp only [R, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
        s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
        A, B, Y, map_sub, MvPolynomial.eval_X, s2v_hardt2_insert_bound,
        s2v_hardt2_insert_free, s, Fin.cons_zero, Fin.cons_one]
    · constructor
      · rintro ⟨hlo, hup⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨hlo, hup⟩
        exact ⟨by linarith, by linarith⟩
    · constructor
      · rintro ⟨hlo, hup⟩
        linarith
      · intro he
        rw [he]
        exact ⟨by linarith, by linarith⟩
  obtain ⟨F, hF⟩ := s2v_hardt6rb_section_substitution C s g hg Fin.succ R
  refine ⟨F, ?_⟩
  intro z
  rw [hF]
  exact exists_congr (fun x => and_congr_right (fun _ => hR x z))

end HodgeLean.Foundations.Program
