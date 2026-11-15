import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Geometric simplex lifts along injective affine maps. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_lift_complex {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    ∃ L : Geometry.SimplicialComplex ℝ F,
      L.faces = (fun s : Finset E => s.image f) '' K.faces ∧
      L.faces.Finite ∧ L.space = f '' K.space := by
  let L : Geometry.SimplicialComplex ℝ F :=
    { toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map f
      indep := by
        rintro t ⟨s, hs, rfl⟩
        have hi := ((K.indep hs).map' f hf).range
        have he : Set.range (f ∘ (Subtype.val : {x : E // x ∈ s} → E)) =
            (↑(s.image f) : Set F) := by
          ext y
          simp [Function.comp_def]
        rw [he] at hi
        exact hi
      inter_subset_convexHull := by
        rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        simp only [Finset.coe_image]
        rw [← f.image_convexHull, ← f.image_convexHull,
          ← Set.image_inter hf, ← Set.image_inter hf, ← f.image_convexHull]
        exact Set.image_mono (K.inter_subset_convexHull ha hb) }
  refine ⟨L, rfl, hK.image _, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨s, hs, hys⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
    obtain ⟨t, ht, rfl⟩ := hs
    rw [Finset.coe_image, ← f.image_convexHull] at hys
    obtain ⟨x, hx, hxy⟩ := hys
    exact ⟨x, K.convexHull_subset_space ht hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    refine Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s.image f, ⟨s, hs, rfl⟩, ?_⟩
    rw [Finset.coe_image, ← f.image_convexHull]
    exact ⟨x, hxs, rfl⟩

end HodgeLean.Foundations.Program
