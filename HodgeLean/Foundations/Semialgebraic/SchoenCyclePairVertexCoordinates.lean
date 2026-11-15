import HodgeLean.Foundations.Program.SchoenTowerHardt6RbVertexInterpolation

/-! Continuous vertex coordinates on finite geometric complexes.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Vertex interpolation gives continuous coordinates with their exact values on each simplex. -/
theorem s2e_pair_vertex_coordinates {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ c : E → E → ℝ,
      (∀ a, Continuous (fun x : K.space => c a x.val)) ∧
      (∀ a (s : Finset E) (hs : s ∈ K.faces) (w : stdSimplex ℝ s),
        c a (∑ i, w.val i • i.val) =
          if ha : a ∈ s then w.val ⟨a, ha⟩ else 0) := by
  classical
  have hex (a : E) := s2v_hardt6rb_vertex_interpolation K hK
    (fun v => if v = a then 1 else 0)
  choose c hc hvert haff using hex
  refine ⟨c, hc, ?_⟩
  intro a s hs w
  rw [haff a s hs w]
  have hv (i : s) : c a i.val = if i.val = a then 1 else 0 :=
    hvert a i.val (K.down_closed hs
      (Finset.singleton_subset_iff.mpr i.property) (Finset.singleton_nonempty _))
  simp_rw [hv]
  by_cases ha : a ∈ s
  · rw [dite_eq_left ha]
    rw [Finset.sum_eq_single (⟨a, ha⟩ : s)]
    · simp only [ite_true, mul_one]
    · intro b _ hb
      have hba : b.val ≠ a := fun h => hb (Subtype.ext h)
      rw [ite_eq_right hba, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [dite_eq_right ha]
    apply Finset.sum_eq_zero
    intro b _
    have hba : b.val ≠ a := fun h => ha (h ▸ b.property)
    rw [ite_eq_right hba, mul_zero]

end Semialgebraic.CompatibleTriangulation.Helpers
