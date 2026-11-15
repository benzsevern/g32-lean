import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCylinderLabels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceCover

/-! Compact-carrier points are covered by the actual graph and adjacent-band cells over the prepared base. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_cell_cover {n q : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (F : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hF : IsCompact F)
    (hbase : ∀ z ∈ F, ∃ x ∈ L.space, ∀ i, z i.succ = β x i)
    (C : Fin q → s2v_t11b_Formula n) (hC : ∀ j, (C j).realize.Nonempty)
    (r : Fin q → ℕ) (ψ : (j : Fin q) → Fin (r j) → (C j).realize → ℝ)
    (hm : ∀ j x, StrictMono (fun a => ψ j a x))
    (g : (j : Fin q) → Fin (r j) → s2v_t11b_Formula (n + 1))
    (band : (j : Fin q) → Fin (r j + 1) → s2v_t11b_Formula (n + 1))
    (hg : ∀ j a z, z ∈ (g j a).realize ↔ ∃ x : (C j).realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = ψ j a x)
    (hb : ∀ j a z, z ∈ (band j a).realize ↔ ∃ x : (C j).realize,
      (∀ i, z i.succ = x.val i) ∧
      (∀ i : Fin (r j), i.val < a.val → ψ j i x < z 0) ∧
      (∀ i : Fin (r j), a.val ≤ i.val → z 0 < ψ j i x))
    (hband : ∀ j a, (band j a).realize ⊆ F ∨ Disjoint (band j a).realize F)
    (parent : L.faces → Fin q)
    (hp : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) → β x ∈ (C (parent s)).realize)
    (f : (s : L.faces) → Fin (r (parent s)) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hagree : ∀ (s : L.faces) (a : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))),
      f s a x = ψ (parent s) a ⟨β x, hp s x hx⟩)
    (c : (s : L.faces) →
      (Fin (r (parent s)) ⊕ {p : Fin (r (parent s)) × Fin (r (parent s)) //
        p.1.val + 1 = p.2.val}) → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hc : ∀ s a, c s a = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))),
      (∀ i, z i.succ = β x i) ∧
      match a with
      | .inl i => z 0 = f s i x
      | .inr p => f s p.val.1 x < z 0 ∧ z 0 < f s p.val.2 x}) :
    e '' F ⊆ ⋃ (i : (s : L.faces) ×
      (Fin (r (parent s)) ⊕ {p : Fin (r (parent s)) × Fin (r (parent s)) //
        p.1.val + 1 = p.2.val})), c i.1 i.2 := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, hzbase⟩ := hbase z hz
  obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face L hx
  let sL : L.faces := ⟨s, hs⟩
  let aC : (C (parent sL)).realize := ⟨β x, hp sL x hxs⟩
  obtain ⟨a, ha⟩ := s2v_hardt6rb_compact_cylinder_labels (C (parent sL)) (hC (parent sL))
    (ψ (parent sL)) (hm (parent sL)) (g (parent sL)) (band (parent sL))
    (hg (parent sL)) (hb (parent sL)) F hF (hband (parent sL)) aC z hzbase hz
  have hlabel : match a with
      | .inl i => z 0 = f sL i x
      | .inr p => f sL p.val.1 x < z 0 ∧ z 0 < f sL p.val.2 x := by
    cases a with
    | inl i => exact ha.trans (hagree sL i x hxs).symm
    | inr p =>
      change f sL p.val.1 x < z 0 ∧ z 0 < f sL p.val.2 x
      rw [hagree sL p.val.1 x hxs, hagree sL p.val.2 x hxs]
      exact ha
  apply Set.mem_iUnion.mpr
  refine ⟨⟨sL, a⟩, ?_⟩
  rw [hc]
  exact ⟨z, ⟨x, hxs, hzbase, by cases a <;> exact hlabel⟩, rfl⟩

end HodgeLean.Foundations.Program
