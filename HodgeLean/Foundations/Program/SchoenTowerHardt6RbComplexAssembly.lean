import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology

/-! Finite geometric assembly from compatible face families. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_assemble_complex {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Finite ι]
    (C : ι → Geometry.SimplicialComplex ℝ E)
    (hfinite : ∀ i, (C i).faces.Finite)
    (hcross : ∀ i j s t, s ∈ (C i).faces → t ∈ (C j).faces →
      convexHull ℝ (↑s : Set _) ∩ convexHull ℝ (↑t : Set _) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set _))) :
    ∃ K : Geometry.SimplicialComplex ℝ E,
      K.faces = ⋃ i, (C i).faces ∧ K.faces.Finite ∧
      K.space = ⋃ i, (C i).space := by
  let K : Geometry.SimplicialComplex ℝ E :=
    { faces := ⋃ i, (C i).faces
      isRelLowerSet_faces := by
        intro s hs
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        refine ⟨(C i).nonempty_of_mem_faces hi, ?_⟩
        intro t hts ht
        exact Set.mem_iUnion.mpr ⟨i, (C i).down_closed hi hts ht⟩
      indep := by
        intro s hs
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        exact (C i).indep hi
      inter_subset_convexHull := by
        intro s t hs ht
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
        exact hcross i j s t hi hj }
  refine ⟨K, rfl, Set.finite_iUnion hfinite, ?_⟩
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion,
    K]
  constructor
  · rintro ⟨s, ⟨i, hi⟩, hx⟩
    exact ⟨i, s, hi, hx⟩
  · rintro ⟨i, s, hi, hx⟩
    exact ⟨s, ⟨i, hi⟩, hx⟩

theorem s2v_hardt6rb_complex_isCompact {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) : IsCompact K.space := by
  exact hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

end HodgeLean.Foundations.Program
