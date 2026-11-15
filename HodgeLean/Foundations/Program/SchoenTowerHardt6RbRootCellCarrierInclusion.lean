import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidIntrinsic

/-! Whole root carrier incidence is exactly base-face inclusion and the two restricted endpoint inequalities. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_carrier_inclusion {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → E → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → f s i x = f t (ρ s t hts i) x)
    (s t : L.faces) (a : s2v_hardt6rb_RootLabel (r s)) (b : s2v_hardt6rb_RootLabel (r t)) :
    ({p : E × ℝ | p.1 ∈ convexHull ℝ (t.val : Set E) ∧
      f t (s2v_hardt6rb_rootLabelLower b) p.1 ≤ p.2 ∧ p.2 ≤ f t (s2v_hardt6rb_rootLabelUpper b) p.1} ⊆
      {p : E × ℝ | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1}) ↔
    ∃ hts : t.val ⊆ s.val,
      ρ s t hts (s2v_hardt6rb_rootLabelLower a) ≤ s2v_hardt6rb_rootLabelLower b ∧
      s2v_hardt6rb_rootLabelUpper b ≤ ρ s t hts (s2v_hardt6rb_rootLabelUpper a) := by
  constructor
  · intro hsub
    let x := t.val.centroid ℝ id
    have hx := s2v_hardt6rb_centroid_intrinsic t.val (L.nonempty_of_mem_faces t.property)
    have hxH := intrinsicInterior_subset hx
    have ho := hm t x hxH (s2v_hardt6rb_root_label_endpoints b).1
    have hlo := hsub (show (x, f t (s2v_hardt6rb_rootLabelLower b) x) ∈ _ from ⟨hxH, le_rfl, ho⟩)
    have hhi := hsub (show (x, f t (s2v_hardt6rb_rootLabelUpper b) x) ∈ _ from ⟨hxH, ho, le_rfl⟩)
    have hts := s2v_hardt6rb_open_face_subset_of_mem_face L t.val s.val t.property s.property hx hlo.1
    refine ⟨hts, (hs t x hx).le_iff_le.mp ?_, (hs t x hx).le_iff_le.mp ?_⟩
    · rw [← hρ s t hts _ x hxH]
      exact hlo.2.1
    · rw [← hρ s t hts _ x hxH]
      exact hhi.2.2
  · rintro ⟨hts, hlo, hhi⟩ p ⟨hx, hp⟩
    refine ⟨convexHull_mono (Finset.coe_subset.mpr hts) hx, ?_, ?_⟩
    · rw [hρ s t hts _ p.1 hx]
      exact (hm t p.1 hx hlo).trans hp.1
    · rw [hρ s t hts _ p.1 hx]
      exact hp.2.trans (hm t p.1 hx hhi)

end HodgeLean.Foundations.Program
