import HodgeLean.Foundations.QuotientDuality.ProperCycleSkeletonLocalPurity

/-! # Actual closed dimension filtrations of finite geometric subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual union of faces with bounded vertex cardinality is closed in the ambient geometric complex.
Source: Munkres, Elements of Algebraic Topology, section 2, finite subcomplexes and skeleta.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_isClosed {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) (i : ℕ) :
    IsClosed {z : K.space | ∃ s ∈ D.faces, s.card ≤ i ∧
      z.val ∈ convexHull ℝ (s : Set E)} := by
  classical
  let F : Set (Finset E) := {s ∈ D.faces | s.card ≤ i}
  have hF : F.Finite := hD.subset (fun _ h => h.1)
  have hc := hF.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  have he : (⋃ s ∈ F, convexHull ℝ (s : Set E)) =
      {z : E | ∃ s ∈ D.faces, s.card ≤ i ∧ z ∈ convexHull ℝ (s : Set E)} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, F]
    tauto
  rw [he] at hc
  exact hc.isClosed.preimage continuous_subtype_val

/-- The actual closed skeleton filtration uses the original finite geometric faces and their real dimensions.
Source: Munkres, Elements of Algebraic Topology, section 2, finite subcomplex skeleta.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_skeleton_filtration {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) : ℕ → Closeds K.space :=
  fun i => ⟨{z | ∃ s ∈ D.faces, s.card ≤ i ∧ z.val ∈ convexHull ℝ (s : Set E)},
    properCycle_subcomplex_skeleton_isClosed K D hD i⟩

/-- The actual dimension filtration starts with empty support.
Source: Munkres, Elements of Algebraic Topology, section 2, nonempty simplex vertex sets.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_zero {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) :
    properCycle_subcomplex_skeleton_filtration K D hD 0 = ⊥ := by
  ext z
  constructor
  · rintro ⟨s, hs, hc, _⟩
    have hp := Finset.card_pos.mpr (D.nonempty_of_mem_faces hs)
    omega
  · intro hz
    exact hz.elim

/-- Actual geometric skeleta form an increasing sequence of closed supports.
Source: Munkres, Elements of Algebraic Topology, section 2, subcomplex skeleta.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_step {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) (i : ℕ) :
    properCycle_subcomplex_skeleton_filtration K D hD i ≤
      properCycle_subcomplex_skeleton_filtration K D hD (i + 1) := by
  rintro z ⟨s, hs, hc, hz⟩
  exact ⟨s, hs, by omega, hz⟩

/-- A vertex-cardinality bound makes the final actual skeleton equal to the original subcomplex carrier.
Source: Munkres, Elements of Algebraic Topology, section 2, finite subcomplex dimension.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_carrier {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) (m : ℕ)
    (hdim : ∀ s ∈ D.faces, s.card ≤ m) :
    (properCycle_subcomplex_skeleton_filtration K D hD m : Set K.space) =
      {z : K.space | z.val ∈ D.space} := by
  ext z
  constructor
  · rintro ⟨s, hs, _, hz⟩
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hz⟩
  · intro hz
    obtain ⟨s, hs, hz⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    exact ⟨s, hs, hdim s hs, hz⟩

end HodgeLean.Foundations.QuotientDuality
