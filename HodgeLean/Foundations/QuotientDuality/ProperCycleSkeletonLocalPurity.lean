import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleGeometricFacePurity

/-! # Actual local purity on finite subcomplex skeleton layers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A dimension skeleton locally equals the given open face, so its supported groups vanish in the ambient range.
Source: Munkres, Elements of Algebraic Topology, section 2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_cofinal_vanishing {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space,
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (s : Finset E) (hs : s ∈ D.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (n : ℕ) (hbound : n + s.card ≤ N) (P : Opens K.space) (hxP : x ∈ P) :
    ∃ W : Opens K.space, W ≤ P ∧ x ∈ W ∧ ∀ j : ℕ, j ≤ n →
      IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set K.space)
          {z : K.space | ∃ q ∈ D.faces, q.card ≤ s.card ∧
            z.val ∈ convexHull ℝ (q : Set E)}) j) := by
  classical
  obtain ⟨O, hxO, hO⟩ := properCycle_geometric_face_incidence_neighborhood K hK s (hDK hs) x hx
  obtain ⟨W, hWP, hxW, hzero⟩ := properCycle_geometric_face_cofinal_vanishing
    K hK V hV N hvan s (hDK hs) x hx n hbound (P ⊓ O) ⟨hxP, hxO⟩
  refine ⟨W, hWP.trans inf_le_left, hxW, ?_⟩
  intro j hj
  let A : Set K.space := {z | ∃ q ∈ D.faces, q.card ≤ s.card ∧
    z.val ∈ convexHull ℝ (q : Set E)}
  let F : Set K.space := {z | z.val ∈ convexHull ℝ (s : Set E)}
  have hlocal (z : W) : (z : K.space) ∈ A ↔ (z : K.space) ∈ F := by
    constructor
    · rintro ⟨q, hq, hcard, hz⟩
      have hsq : s ⊆ q := hO ⟨z.val, (hWP z.property).2⟩ q (hDK hq) hz
      have heq : s = q := Finset.eq_of_subset_of_card_le hsq hcard
      change z.val.val ∈ convexHull ℝ (s : Set E)
      simpa only [heq] using hz
    · intro hz
      exact ⟨s, hs, le_rfl, hz⟩
  let e : neighborhoodSupportComplementPair (W : Set K.space) A ≅
      neighborhoodSupportComplementPair (W : Set K.space) F :=
    TopPair.isoOfSubset (Homeomorph.refl W) (fun z => not_congr (hlocal z).symm)
  let H := (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) j).mapIso
    (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso e.symm))
  exact (hzero j hj).of_iso H

end HodgeLean.Foundations.QuotientDuality
