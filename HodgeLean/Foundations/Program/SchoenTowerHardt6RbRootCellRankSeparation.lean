import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellLabelSeparation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment

/-! The geometric rank orders root cells so a preceding distinct carrier misses each intrinsic open cell. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_rank_separation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → E → ℝ)
    (hf : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) →
      StrictMono (fun i => f s i x))
    (s t : L.faces) (a : s2v_hardt6rb_RootLabel (r s)) (b : s2v_hardt6rb_RootLabel (r t))
    (hrank : 2 * t.val.card + s2v_hardt6rb_rootLabelStep b ≤
      2 * s.val.card + s2v_hardt6rb_rootLabelStep a)
    (p : E × ℝ)
    (hs : p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)))
    (ht : p.1 ∈ convexHull ℝ (t.val : Set E))
    (ha : match a with
      | .inl i => p.2 = f s i p.1
      | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1)
    (hb : f t (s2v_hardt6rb_rootLabelLower b) p.1 ≤ p.2 ∧
      p.2 ≤ f t (s2v_hardt6rb_rootLabelUpper b) p.1) :
    (⟨t, b⟩ : (u : L.faces) × s2v_hardt6rb_RootLabel (r u)) = ⟨s, a⟩ := by
  have hst := s2v_hardt6rb_open_face_subset_of_mem_face L s.val t.val s.property t.property hs ht
  have hda := (s2v_hardt6rb_root_label_endpoints a).2.2
  have hdb := (s2v_hardt6rb_root_label_endpoints b).2.2
  have hcard : t.val.card ≤ s.val.card := by omega
  have he : s = t := Subtype.ext (Finset.eq_of_subset_of_card_le hst hcard)
  subst t
  have hstep : s2v_hardt6rb_rootLabelStep b ≤ s2v_hardt6rb_rootLabelStep a := by omega
  have hba := s2v_hardt6rb_root_cell_label_separation (fun i => f s i p.1) (hf s p.1 hs)
    p.2 a b hstep hb (by cases a <;> exact ha)
  exact congrArg (Sigma.mk s) hba

end HodgeLean.Foundations.Program
