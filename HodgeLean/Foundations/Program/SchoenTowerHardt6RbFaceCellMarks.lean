import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCellRestrictionImage
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdjacentBandFormula
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Intrinsic

/-! The entire refined face-cell family retains the original Boolean marks under its actual ambient map. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_cell_marks {n q m : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (C : Fin q → s2v_t11b_Formula n) (r : Fin q → ℕ)
    (ψ : (j : Fin q) → Fin (r j) → (C j).realize → ℝ)
    (hm : ∀ j x, StrictMono (fun a => ψ j a x))
    (g : (j : Fin q) → Fin (r j) → s2v_t11b_Formula (n + 1))
    (band : (j : Fin q) → Fin (r j + 1) → s2v_t11b_Formula (n + 1))
    (hg : ∀ j a z, z ∈ (g j a).realize ↔ ∃ x : (C j).realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = ψ j a x)
    (hb : ∀ j a z, z ∈ (band j a).realize ↔ ∃ x : (C j).realize,
      (∀ i, z i.succ = x.val i) ∧
      (∀ i : Fin (r j), i.val < a.val → ψ j i x < z 0) ∧
      (∀ i : Fin (r j), a.val ≤ i.val → z 0 < ψ j i x))
    (M : Fin m → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hgm : ∀ j a k, (g j a).realize ⊆ M k ∨ Disjoint (g j a).realize (M k))
    (hbm : ∀ j a k, (band j a).realize ⊆ M k ∨ Disjoint (band j a).realize (M k))
    (parent : L.faces → Fin q)
    (hp : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
        β x ∈ (C (parent s)).realize)
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
    ∀ s a k, c s a ⊆ e '' M k ∨ Disjoint (c s a) (e '' M k) := by
  have transfer (A B : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (hS : S ⊆ e '' A) (hAB : A ⊆ B ∨ Disjoint A B) :
      S ⊆ e '' B ∨ Disjoint S (e '' B) := by
    rcases hAB with h | h
    · exact Or.inl (hS.trans (Set.image_mono h))
    · exact Or.inr ((Set.disjoint_image_of_injective e.injective h).mono_left hS)
  intro s a k
  cases a with
  | inl i =>
    have hr := s2v_hardt6rb_cell_restriction_image (C (parent s)).realize
      (intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))) β (hp s)
      (ψ (parent s) i) (ψ (parent s) i) (f s i) (f s i)
      (hagree s i) (hagree s i) true (g (parent s) i) (hg (parent s) i)
      e (c s (.inl i)) (hc s (.inl i))
    apply transfer _ _ _ ?_ (hgm (parent s) i k)
    rw [hr]
    exact Set.image_mono Set.inter_subset_left
  | inr p =>
    have hS := s2v_hardt6rb_adjacent_band_formula (C (parent s)) (ψ (parent s))
      (hm (parent s)) (band (parent s)) (hb (parent s)) p.val.1 p.val.2 p.property
    have hr := s2v_hardt6rb_cell_restriction_image (C (parent s)).realize
      (intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))) β (hp s)
      (ψ (parent s) p.val.1) (ψ (parent s) p.val.2) (f s p.val.1) (f s p.val.2)
      (hagree s p.val.1) (hagree s p.val.2) false (band (parent s) p.val.2.castSucc) hS
      e (c s (.inr p)) (hc s (.inr p))
    apply transfer _ _ _ ?_ (hbm (parent s) p.val.2.castSucc k)
    rw [hr]
    exact Set.image_mono Set.inter_subset_left

end HodgeLean.Foundations.Program
