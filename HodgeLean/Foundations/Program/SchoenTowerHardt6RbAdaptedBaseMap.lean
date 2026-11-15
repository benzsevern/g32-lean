import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMarkedFaceMembership
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubtypeTotalExtension
import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Analysis.Convex.Topology

/-! A compatible base triangulation constructs one actual ambient base map and a root-cell parent for every face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adapted_base_map {n q : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (P : Set (EuclideanSpace ℝ (Fin n))) (h : L.space ≃ₜ P)
    (C : Fin q → Set (EuclideanSpace ℝ (Fin n))) (hcover : (⋃ j, C j) = Set.univ)
    (hmarks : ∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
      (↑S : Set _) ⊆ L.faces ∧
      P ∩ C j = (fun x : L.space => (h x).val) ''
        {x : L.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))})
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : L.space,
      (∀ i, z (Fin.castAdd n i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i)) :
    ∃ β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn β L.space ∧ Set.InjOn β L.space ∧ β '' L.space = P ∧
      (∀ x : L.space, β x.val = (h x).val) ∧
      (∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
        (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i)) ∧
      ∃ parent : L.faces → Fin q, ∀ s x,
        x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)) → β x ∈ C (parent s) := by
  classical
  obtain ⟨β, hβ, he⟩ := s2v_hardt6rb_subtype_total_extension L.space
    (fun x => (h x).val) (continuous_subtype_val.comp h.continuous)
  have hinj : Set.InjOn β L.space := by
    intro x hx y hy hxy
    have hh : h ⟨x, hx⟩ = h ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [← he ⟨x, hx⟩, ← he ⟨y, hy⟩]
      exact hxy
    exact congrArg Subtype.val (h.injective hh)
  have himage : β '' L.space = P := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he ⟨x, hx⟩]
      exact (h ⟨x, hx⟩).property
    · intro hy
      let x := h.symm ⟨y, hy⟩
      refine ⟨x.val, x.property, ?_⟩
      exact (he x).trans (congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩))
  have hgraph : ∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i) := by
    intro z
    rw [hG]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x.val, x.property, hx, by simpa only [he x] using hy⟩
    · rintro ⟨x, hx, hin, hout⟩
      exact ⟨⟨x, hx⟩, hin, by simpa only [he ⟨x, hx⟩] using hout⟩
  choose S hS hsel using hmarks
  have parents (s : L.faces) : ∃ j, ∀ x,
      x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)) → β x ∈ C j := by
    have hne : (convexHull ℝ (↑s.val : Set (EuclideanSpace ℝ (Fin n)))).Nonempty :=
      (L.nonempty_of_mem_faces s.property).to_set.mono (subset_convexHull ℝ _)
    obtain ⟨x, hx⟩ := hne.intrinsicInterior (convex_convexHull ℝ _)
    let xL : L.space := ⟨x, L.convexHull_subset_space s.property (intrinsicInterior_subset hx)⟩
    have hxC : (h xL).val ∈ ⋃ j, C j := by rw [hcover]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
    have hs : s.val ∈ S j :=
      (s2v_hardt6rb_marked_open_face_membership L P (C j) h (S j) (hS j)
        (hsel j) s.val s.property xL hx).mp hj
    refine ⟨j, ?_⟩
    intro y hy
    let yL : L.space := ⟨y, L.convexHull_subset_space s.property (intrinsicInterior_subset hy)⟩
    rw [he yL]
    exact (s2v_hardt6rb_marked_open_face_membership L P (C j) h (S j) (hS j)
      (hsel j) s.val s.property yL hy).mpr hs
  choose parent hp using parents
  exact ⟨β, hβ, hinj, himage, he, hgraph, parent, hp⟩

end HodgeLean.Foundations.Program
