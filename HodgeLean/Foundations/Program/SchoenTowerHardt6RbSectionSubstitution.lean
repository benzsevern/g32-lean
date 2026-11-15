import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools

/-! Simultaneous substitution of finitely many actual section graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_section_substitution {n k N : ℕ}
    (C : s2v_t11b_Formula n) (s : Fin k → C.realize → ℝ)
    (g : Fin k → s2v_t11b_Formula (n + 1))
    (hg : ∀ i z, z ∈ (g i).realize ↔ ∃ x : C.realize,
      (∀ v, z v.succ = x.val v) ∧ z 0 = s i x)
    (idx : Fin n → Fin N) (F : s2v_t11b_Formula (N + k)) :
    ∃ G : s2v_t11b_Formula N, ∀ y, y ∈ G.realize ↔
      ∃ x : C.realize, (∀ v, y (idx v) = x.val v) ∧
        s2v_hardt2_insert k (fun i => s i x) y ∈ F.realize := by
  induction k generalizing N with
  | zero =>
    refine ⟨.inter (s2v_hardt1_rename idx C) F, ?_⟩
    intro y
    change (y ∈ (s2v_hardt1_rename idx C).realize ∧ y ∈ F.realize) ↔ _
    rw [s2v_hardt1_realize_rename]
    constructor
    · rintro ⟨hy, hF⟩
      exact ⟨⟨WithLp.toLp 2 (fun v => y (idx v)), hy⟩, fun _ => rfl, hF⟩
    · rintro ⟨x, hx, hF⟩
      have he : WithLp.toLp 2 (fun v => y (idx v)) = x.val := by
        ext v
        exact hx v
      exact ⟨he.symm ▸ x.property, hF⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := s2v_hardt_cad3_graph_substitution C (s 0) (g 0) (hg 0)
      (fun v => s2v_hardt2_freeIndex N k (idx v)) F
    obtain ⟨G, hG⟩ := ih (fun i => s i.succ) (fun i => g i.succ)
      (fun i => hg i.succ) idx R
    refine ⟨G, ?_⟩
    intro y
    rw [hG]
    constructor
    · rintro ⟨x, hx, hRx⟩
      obtain ⟨x', hx', hF⟩ := (hR _).mp hRx
      have he : x' = x := by
        apply Subtype.ext
        ext v
        exact (hx' v).symm.trans
          ((s2v_hardt2_insert_free _ _ _).trans (hx v))
      subst x'
      exact ⟨x, hx, hF⟩
    · rintro ⟨x, hx, hF⟩
      refine ⟨x, hx, (hR _).mpr ⟨x, ?_, hF⟩⟩
      intro v
      exact (s2v_hardt2_insert_free _ _ _).trans (hx v)

end HodgeLean.Foundations.Program
