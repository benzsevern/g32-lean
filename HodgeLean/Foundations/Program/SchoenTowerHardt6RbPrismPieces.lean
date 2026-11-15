import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismIndependence
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexComplex

/-! Finite simplex complexes covering a variable-height band over one simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_piece_complexes {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (hlu : ∀ i, l i ≤ u i) :
    ∃ C : Fin (m + 1) → Geometry.SimplicialComplex ℝ (E × ℝ),
      (∀ j s, s ∈ (C j).faces ↔
        (↑s : Set (E × ℝ)) ⊆
          (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
            ((fun i => (v i, u i)) '' {i | i ≤ j})) ∧ s.Nonempty) ∧
      (∀ j, (C j).faces.Finite) ∧
      (∀ j, (C j).space = convexHull ℝ
        (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
          ((fun i => (v i, u i)) '' {i | i ≤ j}))) ∧
      ∀ (w : stdSimplex ℝ (Fin (m + 1))) (y : ℝ),
        (∑ i, w.val i * l i) ≤ y → y ≤ (∑ i, w.val i * u i) →
        (∑ i, w.val i • v i, y) ∈ ⋃ j, (C j).space := by
  classical
  let S : Fin (m + 1) → Set (E × ℝ) := fun j =>
    ((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
      ((fun i => (v i, u i)) '' {i | i ≤ j})
  have hS (j) : (S j).Finite :=
    ((Set.toFinite {i : Fin (m + 1) | j ≤ i}).image _).union
      ((Set.toFinite {i : Fin (m + 1) | i ≤ j}).image _)
  have hp (j) : ∃ K : Geometry.SimplicialComplex ℝ (E × ℝ),
      (∀ s, s ∈ K.faces ↔ (↑s : Set (E × ℝ)) ⊆ S j ∧ s.Nonempty) ∧
      K.faces.Finite ∧ K.space = convexHull ℝ (S j) := by
    have hi : AffineIndependent ℝ (fun x : (hS j).toFinset => (x : E × ℝ)) := by
      let e : (hS j).toFinset ↪ S j :=
        ⟨fun x => ⟨x.val, (hS j).mem_toFinset.mp x.property⟩,
          fun a b h => Subtype.ext (congrArg (fun x : S j => x.val) h)⟩
      exact (s2v_hardt6rb_prism_staircase_independent v hv l u j).comp_embedding e
    obtain ⟨K, hfaces, hfinite, hspace⟩ := s2v_hardt6rb_simplex_complex (hS j).toFinset hi
    refine ⟨K, ?_, hfinite, by simpa only [Set.Finite.coe_toFinset] using hspace⟩
    intro s
    rw [hfaces]
    constructor
    · rintro ⟨hs, hne⟩
      exact ⟨fun x hx => (hS j).mem_toFinset.mp (hs hx), hne⟩
    · rintro ⟨hs, hne⟩
      exact ⟨fun x hx => (hS j).mem_toFinset.mpr (hs hx), hne⟩
  choose C hfaces hfinite hspace using hp
  refine ⟨C, hfaces, hfinite, hspace, ?_⟩
  intro w y hylo hyhi
  obtain ⟨j, hj⟩ := s2v_hardt6rb_prism_staircase_cover v l u hlu w hylo hyhi
  exact Set.mem_iUnion.mpr ⟨j, (hspace j).symm ▸ hj⟩

end HodgeLean.Foundations.Program
