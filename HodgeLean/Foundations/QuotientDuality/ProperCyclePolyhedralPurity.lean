import HodgeLean.Foundations.QuotientDuality.ProperCycleSkeletonFiltration
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalLayerFiltration
import Mathlib.Topology.EMetricSpace.Paracompact

/-! # Actual supported purity of finite polyhedral subspaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite actual subcomplex has zero supported cohomology below ambient orientation degree minus its dimension.
Source: Munkres, Elements of Algebraic Topology, section 2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_subcomplex_relative_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space,
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (m : ℕ) (hdim : ∀ s ∈ D.faces, s.card ≤ m)
    (n : ℕ) (hbound : n + m ≤ N) (U : Opens K.space) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space}) n) := by
  classical
  have hD : D.faces.Finite := hK.subset hDK
  let B := properCycle_subcomplex_skeleton_filtration K D hD
  letI : ∀ P : Opens K.space, ParacompactSpace P := fun _ => inferInstance
  have hz : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set K.space) (B m : Set K.space)) n) := by
    apply properCycle_filtration_relative_vanishes_of_local_layers (TopCat.of K.space) B
      (properCycle_subcomplex_skeleton_zero K D hD) m n
      (fun i _ => properCycle_subcomplex_skeleton_step K D hD i) ?_ U
    intro i hi x hxB hxnot P hxP
    obtain ⟨q, hq, hcardq, hxq⟩ := hxB
    have hxD : x.val ∈ D.space := Geometry.SimplicialComplex.mem_space_iff.mpr ⟨q, hq, hxq⟩
    obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face D hxD
    have hsq : s ⊆ q := s2v_hardt6rb_open_face_subset_of_mem_face D s q hs hq hxs hxq
    have hcard : s.card ≤ i + 1 := (Finset.card_le_card hsq).trans hcardq
    have hncard : ¬ s.card ≤ i := fun h => hxnot ⟨s, hs, h, intrinsicInterior_subset hxs⟩
    have heq : s.card = i + 1 := by omega
    obtain ⟨W, hWP, hxW, hzero⟩ := properCycle_subcomplex_skeleton_cofinal_vanishing
      K D hK hDK V hV N hvan s hs x hxs (n + (m - (i + 1))) (by omega) P hxP
    refine ⟨W, hWP, hxW, ?_⟩
    intro j hj
    change IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set K.space)
        {z : K.space | ∃ q ∈ D.faces, q.card ≤ i + 1 ∧
          z.val ∈ convexHull ℝ (q : Set E)}) j)
    simpa only [heq] using hzero j hj
  have hcar : (B m : Set K.space) = {z : K.space | z.val ∈ D.space} :=
    properCycle_subcomplex_skeleton_carrier K D hD m hdim
  rw [hcar] at hz
  exact hz

end HodgeLean.Foundations.QuotientDuality
