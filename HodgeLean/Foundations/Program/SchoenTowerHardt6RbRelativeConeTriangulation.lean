import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeComplex
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeFaceRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactRayEndpoint

/-! A prescribed finite boundary triangulation extends over a compact convex carrier by coning. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_relative_cone_triangulation {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hcompact : IsCompact C) (hconv : Convex ℝ C)
    (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hboundary : K.space = C \ intrinsicInterior ℝ C) (hne : K.space.Nonempty) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = C ∧
      K.faces ⊆ L.faces ∧
      (∀ s, s ∈ L.faces ↔ ∃ t ∈ K.faces, s ⊆ insert a t ∧ s.Nonempty) ∧
      (∀ s ∈ L.faces, s ∈ K.faces ↔ a ∉ s) := by
  obtain ⟨L, hLf, hfaces, hKL, hspace⟩ := s2v_hardt6rb_cone_complex C hconv a ha K hK
    (by rw [hboundary])
  have haK : a ∉ K.space := by
    rw [hboundary]
    exact fun hx => hx.2 ha
  refine ⟨L, hLf, ?_, hKL, hfaces, s2v_hardt6rb_cone_face_restriction K L a haK hfaces⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, u, hu, rfl⟩ := (hspace x).mp hx
    have hyC : y ∈ C := (hboundary ▸ hy).1
    exact hconv.segment_subset (intrinsicInterior_subset ha) hyC (lineMap_mem_segment ℝ a y hu)
  · intro hx
    apply (hspace x).mpr
    by_cases hxa : x = a
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp only [hxa, AffineMap.lineMap_apply_zero]⟩
    · obtain ⟨y, hy, u, hu, he⟩ := s2v_hardt6rb_compact_ray_endpoint C hcompact a
        (intrinsicInterior_subset ha) x hx hxa
      exact ⟨y, hboundary.symm ▸ hy, u, hu, he⟩

end HodgeLean.Foundations.Program
