import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabels

/-! A root cell of no greater fiber dimension cannot meet another root cell's open part. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_label_separation {r : ℕ}
    (f : Fin r → ℝ) (hf : StrictMono f) (t : ℝ)
    (a b : s2v_hardt6rb_RootLabel r)
    (hd : s2v_hardt6rb_rootLabelStep b ≤ s2v_hardt6rb_rootLabelStep a)
    (hb : f (s2v_hardt6rb_rootLabelLower b) ≤ t ∧ t ≤ f (s2v_hardt6rb_rootLabelUpper b))
    (ha : match a with
      | .inl i => t = f i
      | .inr p => f p.val.1 < t ∧ t < f p.val.2) : b = a := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have ht : t = f j := le_antisymm hb.2 hb.1
      exact congrArg Sum.inl (hf.injective (ht.symm.trans ha))
    | inr q => exact False.elim (Nat.not_succ_le_zero 0 hd)
  | inr p =>
    have hn (i : Fin r) : t ≠ f i := by
      intro hi
      have hh := s2v_hardt6rb_ordered_cell_labels f hf t (.inl i) (.inr p) hi ha
      cases hh
    cases b with
    | inl i => exact False.elim (hn i (le_antisymm hb.2 hb.1))
    | inr q =>
      apply s2v_hardt6rb_ordered_cell_labels f hf t (.inr q) (.inr p) _ ha
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm (hn q.val.1)), lt_of_le_of_ne hb.2 (hn q.val.2)⟩

end HodgeLean.Foundations.Program
