import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalPrism
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbLiftedHullWeights

/-! The exact carrier of a globally assembled ordered band complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_global_prism_carrier {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (l u : E → ℝ)
    (hlu : ∀ x ∈ K.vertices, l x ≤ u x)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hfaces : ∀ r, r ∈ L.faces ↔ ∃ s ∈ K.faces, ∃ j : s,
      (↑r : Set (E × ℝ)) ⊆
        (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
          ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j})) ∧ r.Nonempty) :
    L.space = {p | ∃ s ∈ K.faces, ∃ w : stdSimplex ℝ s,
      (∑ i, w.val i • i.val) = p.1 ∧
      (∑ i, w.val i * l i.val) ≤ p.2 ∧ p.2 ≤ ∑ i, w.val i * u i.val} := by
  classical
  have hlocal (s : Finset E) (hs : s ∈ K.faces) (i : s) : l i.val ≤ u i.val :=
    hlu i.val (K.down_closed hs (Finset.singleton_subset_iff.mpr i.property)
      (Finset.singleton_nonempty _))
  ext p
  constructor
  · intro hp
    obtain ⟨r, hr, hpr⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
    obtain ⟨s, hs, j, hrj, _⟩ := (hfaces r).mp hr
    have hpall : p ∈ convexHull ℝ
        (Set.range (fun i : s => (i.val, l i.val)) ∪
          Set.range (fun i : s => (i.val, u i.val))) := by
      apply convexHull_mono ?_ hpr
      intro x hx
      rcases hrj hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, rfl⟩
    obtain ⟨w, hw, hlo, hup⟩ := s2v_hardt6rb_lifted_hull_weights
      (fun i : s => i.val) (fun i => l i.val) (fun i => u i.val) (hlocal s hs) p hpall
    exact ⟨s, hs, w, hw, hlo, hup⟩
  · rintro ⟨s, hs, w, hw, hlo, hup⟩
    letI : Nonempty s := by
      obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
      exact ⟨⟨x, hx⟩⟩
    obtain ⟨j, hj⟩ := s2v_hardt6rb_ordered_prism_cover (fun i : s => i.val)
      (fun i => l i.val) (fun i => u i.val) (hlocal s hs) w p.2 hlo hup
    rw [hw] at hj
    let S : Set (E × ℝ) :=
      (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
        ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j}))
    have hS : S.Finite := ((Set.toFinite {i : s | j ≤ i}).image _).union
      ((Set.toFinite {i : s | i ≤ j}).image _)
    have hpS : p ∈ convexHull ℝ S := by simpa only [Prod.mk.eta] using hj
    have hne : hS.toFinset.Nonempty :=
      Finset.coe_nonempty.mp (by
        rw [Set.Finite.coe_toFinset]
        exact convexHull_nonempty_iff.mp ⟨p, hpS⟩)
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨hS.toFinset, (hfaces _).mpr ⟨s, hs, j, ?_, hne⟩, ?_⟩
    · exact fun x hx => hS.mem_toFinset.mp hx
    · simpa only [Set.Finite.coe_toFinset] using hpS

end HodgeLean.Foundations.Program
