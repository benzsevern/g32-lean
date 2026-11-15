import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFacePartition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Cells above distinct intrinsic open base faces stay disjoint under the actual coordinate maps. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_distinct_face_cells {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : Set.InjOn β L.space)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (s t : L.faces) (hst : s ≠ t)
    (c d : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hc : c ⊆ e '' {z | ∃ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)),
      ∀ i, z i.succ = β x i})
    (hd : d ⊆ e '' {z | ∃ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑t.val : Set _)),
      ∀ i, z i.succ = β x i}) : Disjoint c d := by
  apply Set.disjoint_left.mpr
  intro z hzc hzd
  obtain ⟨u, ⟨x, hx, hux⟩, hu⟩ := hc hzc
  obtain ⟨v, ⟨y, hy, hvy⟩, hv⟩ := hd hzd
  have huv : u = v := e.injective (hu.trans hv.symm)
  have hxyβ : β x = β y := by
    ext i
    exact (hux i).symm.trans ((congrArg (fun w => w i.succ) huv).trans (hvy i))
  have hxL := L.convexHull_subset_space s.property (intrinsicInterior_subset hx)
  have hyL := L.convexHull_subset_space t.property (intrinsicInterior_subset hy)
  have hxy : x = y := hβ hxL hyL hxyβ
  subst y
  obtain ⟨f, hf, huniq⟩ := s2v_hardt6rb_unique_open_face L hxL
  exact hst (Subtype.ext ((huniq s.val ⟨s.property, hx⟩).trans
    (huniq t.val ⟨t.property, hy⟩).symm))

end HodgeLean.Foundations.Program
