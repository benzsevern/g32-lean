import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCofinalChart
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! # Actual neighborhoods excluding faces not containing the given open face -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Around an actual open-face point every incident face contains that face.
Source: Munkres, Elements of Algebraic Topology, section 2, finite geometric complexes and open stars.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_face_incidence_neighborhood {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ U : Opens K.space, x ∈ U ∧ ∀ z : U, ∀ q ∈ K.faces,
      z.val.val ∈ convexHull ℝ (q : Set E) → s ⊆ q := by
  classical
  let O : Set K.space := {z | ∀ q ∈ K.faces, z.val ∈ convexHull ℝ (q : Set E) → s ⊆ q}
  have hO : IsOpen O := by
    have he : O = ⋂ q ∈ hK.toFinset,
        {z : K.space | z.val ∈ convexHull ℝ (q : Set E) → s ⊆ q} := by
      ext z
      simp only [O, Set.mem_setOf_eq, Set.mem_iInter, hK.mem_toFinset]
    rw [he]
    apply isOpen_biInter_finset
    intro q _
    by_cases hsq : s ⊆ q
    · have heq : {z : K.space | z.val ∈ convexHull ℝ (q : Set E) → s ⊆ q} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun _ => hsq
      rw [heq]
      exact isOpen_univ
    · have heq : {z : K.space | z.val ∈ convexHull ℝ (q : Set E) → s ⊆ q} =
          {z : K.space | z.val ∉ convexHull ℝ (q : Set E)} := by
        ext z
        simp only [Set.mem_setOf_eq, hsq, imp_false]
      rw [heq]
      exact ((q.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
        continuous_subtype_val).isOpen_compl
  let U : Opens K.space := ⟨O, hO⟩
  have hxU : x ∈ U := fun q hq hz =>
    s2v_hardt6rb_open_face_subset_of_mem_face K s q hs hq hx hz
  exact ⟨U, hxU, fun z => z.property⟩

end HodgeLean.Foundations.QuotientDuality
