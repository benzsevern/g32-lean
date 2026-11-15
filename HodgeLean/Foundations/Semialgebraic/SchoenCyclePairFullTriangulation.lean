import HodgeLean.Foundations.Program.SchoenTowerHardt6Rb
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbClosedMarkSubcomplex
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCommonSubdivision

/-! Full finite triangulations for compact Boolean pairs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- A compact Boolean pair has a triangulation whose marked subcomplex is full. -/
theorem s2e_pair_boolean_full_triangulation {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize)) :
    ∃ L M : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      L.faces.Finite ∧ M.faces.Finite ∧ M.faces ⊆ L.faces ∧
      (∀ s ∈ L.faces, (∀ x ∈ s, x ∈ M.vertices) → s ∈ M.faces) ∧
      ∃ h : L.space ≃ₜ f.realize,
        ∀ x : L.space, (h x).val ∈ b.realize ↔ x.val ∈ M.space := by
  obtain ⟨K, hK, h, hmarks, _⟩ :=
    s2v_hardt6rb_compatible_triangulation f hf (fun _ : Fin 1 => b)
  obtain ⟨S, hS, hsel⟩ := hmarks 0
  obtain ⟨D, _, hDK, hDmark⟩ := s2v_hardt6rb_closed_mark_subcomplex
    K hK f.realize b.realize h hb S hS hsel
  obtain ⟨L, hL, hLK, hfull⟩ := s2v_hardt6rb_common_full_subdivision K hK
  obtain ⟨M, hM, hML, hMD, hMf⟩ := hfull D hDK
  let e : L.space ≃ₜ K.space := Homeomorph.setCongr hLK
  refine ⟨L, M, hL, hM, hML, hMf, e.trans h, ?_⟩
  intro x
  change (h (e x)).val ∈ b.realize ↔ x.val ∈ M.space
  rw [hDmark, hMD]
  rfl

end Semialgebraic.CompatibleTriangulation.Helpers
