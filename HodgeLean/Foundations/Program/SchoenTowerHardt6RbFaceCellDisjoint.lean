import HodgeLean.Foundations.Program.SchoenTowerHardt6RbDistinctFaceCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedCellLabels

/-! Actual face-root cells form a disjoint family indexed by their base faces and ordered labels. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_cell_disjoint {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : Set.InjOn β L.space)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)) →
      StrictMono (fun a => f s a x))
    (c : (s : L.faces) →
      (Fin (r s) ⊕ {p : Fin (r s) × Fin (r s) // p.1.val + 1 = p.2.val}) →
      Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hc : ∀ s a, c s a = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (↑s.val : Set (EuclideanSpace ℝ (Fin n)))),
      (∀ i, z i.succ = β x i) ∧
      match a with
      | .inl i => z 0 = f s i x
      | .inr p => f s p.val.1 x < z 0 ∧ z 0 < f s p.val.2 x}) :
    ∀ (i j : (s : L.faces) ×
      (Fin (r s) ⊕ {p : Fin (r s) × Fin (r s) // p.1.val + 1 = p.2.val})),
      i ≠ j → Disjoint (c i.1 i.2) (c j.1 j.2) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ hne
  apply Set.disjoint_left.mpr
  intro z hzs hzt
  rw [hc s a] at hzs
  rw [hc t b] at hzt
  obtain ⟨u, ⟨x, hx, hux, ha⟩, hu⟩ := hzs
  obtain ⟨v, ⟨y, hy, hvy, hb⟩, hv⟩ := hzt
  have huv : u = v := e.injective (hu.trans hv.symm)
  have heβ : β x = β y := by
    ext k
    exact (hux k).symm.trans ((congrArg (fun w => w k.succ) huv).trans (hvy k))
  have hxL := L.convexHull_subset_space s.property (intrinsicInterior_subset hx)
  have hyL := L.convexHull_subset_space t.property (intrinsicInterior_subset hy)
  have hxy : x = y := hβ hxL hyL heβ
  subst y
  obtain ⟨vface, hvface, huniq⟩ := s2v_hardt6rb_unique_open_face L hxL
  have hst : s = t := Subtype.ext ((huniq s.val ⟨s.property, hx⟩).trans
    (huniq t.val ⟨t.property, hy⟩).symm)
  subst t
  rw [← huv] at hb
  have hab : a = b := s2v_hardt6rb_ordered_cell_labels (fun k => f s k x) (hf s x hx) (u 0) a b
    (by cases a <;> exact ha) (by cases b <;> exact hb)
  subst b
  exact hne rfl

end HodgeLean.Foundations.Program
