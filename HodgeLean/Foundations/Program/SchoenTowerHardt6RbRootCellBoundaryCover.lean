import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbProperOpenFaceBoundary
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedIntervalCells

/-! Every root cell boundary point lies in an entire lower-rank root carrier contained in the original carrier. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_boundary_cover {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → E → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → f s i x = f t (ρ s t hts i) x)
    (C : (s : L.faces) → s2v_hardt6rb_RootLabel (r s) → Set (E × ℝ))
    (hC : ∀ s a, C s a = {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1})
    (O : (s : L.faces) → s2v_hardt6rb_RootLabel (r s) → Set (E × ℝ))
    (hI : ∀ s a, O s a = {p | p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = f s i p.1 | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1})
    (s : L.faces) (a : s2v_hardt6rb_RootLabel (r s)) (p : E × ℝ)
    (hp : p ∈ C s a \ O s a) :
    ∃ (t : L.faces) (b : s2v_hardt6rb_RootLabel (r t)),
      2 * t.val.card + s2v_hardt6rb_rootLabelStep b < 2 * s.val.card + s2v_hardt6rb_rootLabelStep a ∧
      p ∈ C t b ∧ C t b ⊆ C s a := by
  classical
  have hpc := (Set.ext_iff.mp (hC s a) p).mp hp.1
  have hpn : ¬ (p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = f s i p.1 | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1) :=
    fun h => hp.2 ((Set.ext_iff.mp (hI s a) p).mpr (by cases a <;> exact h))
  by_cases hx : p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E))
  · cases a with
    | inl i => exact False.elim (hpn ⟨hx, le_antisymm hpc.2.2 hpc.2.1⟩)
    | inr q =>
      have he : p.2 = f s q.val.1 p.1 ∨ p.2 = f s q.val.2 p.1 := by
        by_cases hlo : p.2 = f s q.val.1 p.1
        · exact Or.inl hlo
        · right
          by_contra hhi
          exact hpn ⟨hx, lt_of_le_of_ne hpc.2.1 (Ne.symm hlo), lt_of_le_of_ne hpc.2.2 hhi⟩
      have hqle : q.val.1 ≤ q.val.2 := (s2v_hardt6rb_root_label_endpoints (.inr q)).1
      have endpoint (i : Fin (r s)) (hlo : q.val.1 ≤ i) (hhi : i ≤ q.val.2) (he : p.2 = f s i p.1) :
          ∃ (t : L.faces) (b : s2v_hardt6rb_RootLabel (r t)),
            2 * t.val.card + s2v_hardt6rb_rootLabelStep b < 2 * s.val.card + 1 ∧
            p ∈ C t b ∧ C t b ⊆ C s (.inr q) := by
        refine ⟨s, .inl i, Nat.lt_succ_self _, ?_, ?_⟩
        · rw [hC]
          exact ⟨hpc.1, he.ge, he.le⟩
        · intro z hz
          rw [hC] at hz ⊢
          have hzi : z.2 = f s i z.1 := le_antisymm hz.2.2 hz.2.1
          refine ⟨hz.1, ?_, ?_⟩
          · exact (hm s z.1 hz.1 hlo).trans hzi.ge
          · exact hzi.le.trans (hm s z.1 hz.1 hhi)
      rcases he with he | he
      · exact endpoint q.val.1 le_rfl hqle he
      · exact endpoint q.val.2 hqle le_rfl he
  · obtain ⟨t, hts, hxt⟩ := (s2v_hardt6rb_proper_open_face_boundary L s hpc.1).mp hx
    have hxtH := intrinsicInterior_subset hxt
    have hy : f t (ρ s t hts.subset (s2v_hardt6rb_rootLabelLower a)) p.1 ≤ p.2 ∧
        p.2 ≤ f t (ρ s t hts.subset (s2v_hardt6rb_rootLabelUpper a)) p.1 := by
      rw [← hρ s t hts.subset _ p.1 hxtH, ← hρ s t hts.subset _ p.1 hxtH]
      exact hpc.2
    obtain ⟨b, hlo, hhi, hb⟩ : ∃ b : s2v_hardt6rb_RootLabel (r t),
        ρ s t hts.subset (s2v_hardt6rb_rootLabelLower a) ≤ s2v_hardt6rb_rootLabelLower b ∧
        s2v_hardt6rb_rootLabelUpper b ≤ ρ s t hts.subset (s2v_hardt6rb_rootLabelUpper a) ∧
        f t (s2v_hardt6rb_rootLabelLower b) p.1 ≤ p.2 ∧ p.2 ≤ f t (s2v_hardt6rb_rootLabelUpper b) p.1 := by
      rcases (s2v_hardt6rb_ordered_interval_cells (fun i => f t i p.1) (hs t p.1 hxt) _ _ p.2).mp hy with
        ⟨i, hi, hj, he⟩ | ⟨i, j, hij, hi, hj, hiy, hyj⟩
      · exact ⟨.inl i, hi, hj, he.ge, he.le⟩
      · exact ⟨.inr ⟨(i, j), hij⟩, hi, hj, hiy.le, hyj.le⟩
    refine ⟨t, b, ?_, ?_, ?_⟩
    · have hc := Finset.card_lt_card hts
      have hd := (s2v_hardt6rb_root_label_endpoints b).2.2
      omega
    · rw [hC]
      exact ⟨hxtH, hb⟩
    · intro z hz
      rw [hC] at hz ⊢
      refine ⟨convexHull_mono (Finset.coe_subset.mpr hts.subset) hz.1, ?_, ?_⟩
      · rw [hρ s t hts.subset _ z.1 hz.1]
        exact (hm t z.1 hz.1 hlo).trans hz.2.1
      · rw [hρ s t hts.subset _ z.1 hz.1]
        exact hz.2.2.trans (hm t z.1 hz.1 hhi)

end HodgeLean.Foundations.Program
