import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCoherentRootBandModels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabels

/-! Actual graph and adjacent band models preserve their parametrized open parts and all boundary fibers. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_models {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (r : L.faces → ℕ)
    (f g : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ s a, ContinuousOn (f s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hgc : ∀ s a, ContinuousOn (g s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hfm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x))
    (hgm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => g s a x))
    (hf : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (hg : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => g s a x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρf : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      f s a x = f t (ρ s t hts a) x)
    (hρg : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      g s a x = g t (ρ s t hts a) x)
    (s : L.faces) (a : s2v_hardt6rb_RootLabel (r s)) :
    ∃ h : {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ convexHull ℝ (s.val : Set _) ∧
        g s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ g s (s2v_hardt6rb_rootLabelUpper a) p.1} ≃ₜ
      {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ convexHull ℝ (s.val : Set _) ∧
        f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1},
      (∀ p q, h p = q ↔ p.val.1 = q.val.1 ∧
        (p.val.2 - g s (s2v_hardt6rb_rootLabelLower a) p.val.1) *
          (f s (s2v_hardt6rb_rootLabelUpper a) p.val.1 - f s (s2v_hardt6rb_rootLabelLower a) p.val.1) =
        (q.val.2 - f s (s2v_hardt6rb_rootLabelLower a) p.val.1) *
          (g s (s2v_hardt6rb_rootLabelUpper a) p.val.1 - g s (s2v_hardt6rb_rootLabelLower a) p.val.1)) ∧
      (∀ p, (p.val.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∧
          match a with
          | .inl i => p.val.2 = g s i p.val.1
          | .inr q => g s q.val.1 p.val.1 < p.val.2 ∧ p.val.2 < g s q.val.2 p.val.1) ↔
        ((h p).val.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∧
          match a with
          | .inl i => (h p).val.2 = f s i (h p).val.1
          | .inr q => f s q.val.1 (h p).val.1 < (h p).val.2 ∧ (h p).val.2 < f s q.val.2 (h p).val.1)) := by
  obtain ⟨h, hh, hb⟩ := s2v_hardt6rb_coherent_root_band_models L r f g hfc hgc hfm hgm hf hg ρ hρf hρg
    s (s2v_hardt6rb_rootLabelLower a) (s2v_hardt6rb_rootLabelUpper a) (s2v_hardt6rb_root_label_endpoints a).1
  refine ⟨h, hh, ?_⟩
  intro p
  have hbase := ((hh p (h p)).mp rfl).1
  cases a with
  | inl i =>
    constructor
    · intro hp
      exact ⟨hbase ▸ hp.1, le_antisymm (h p).property.2.2 (h p).property.2.1⟩
    · intro hp
      exact ⟨hbase.symm ▸ hp.1, le_antisymm p.property.2.2 p.property.2.1⟩
  | inr q =>
    have hneg (x : EuclideanSpace ℝ (Fin n)) (l u y : ℝ) (hlo : l ≤ y) (hhi : y ≤ u) :
        ¬(x ∉ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∨ y = l ∨ y = u) ↔
        x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∧ l < y ∧ y < u := by
      simp only [not_or, not_not]
      exact ⟨fun hh => ⟨hh.1, lt_of_le_of_ne hlo (Ne.symm hh.2.1), lt_of_le_of_ne hhi hh.2.2⟩,
        fun hh => ⟨hh.1, ne_of_gt hh.2.1, ne_of_lt hh.2.2⟩⟩
    exact (hneg p.val.1 _ _ p.val.2 p.property.2.1 p.property.2.2).symm.trans
      ((not_congr (hb p)).trans (hneg (h p).val.1 _ _ (h p).val.2 (h p).property.2.1 (h p).property.2.2))

end HodgeLean.Foundations.Program
