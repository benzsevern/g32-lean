import HodgeLean.Foundations.QuotientDuality.ProperCycleSkeletonLocalPurity

/-! # Actual face support calculations from concentration only at the specified point -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Ambient local concentration gives cofinal supported vanishing along actual finite geometric face interiors.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_face_cofinal_vanishing_at_point {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hvan : ∀ j : ℕ, j ≠ N →
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (n : ℕ) (hbound : n + s.card ≤ N) (P : Opens K.space) (hxP : x ∈ P) :
    ∃ W : Opens K.space, W ≤ P ∧ x ∈ W ∧ ∀ j : ℕ, j ≤ n →
      IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set K.space)
          {z : K.space | z.val ∈ convexHull ℝ (s : Set E)}) j) := by
  obtain ⟨a, W, Y, y, e, hWP, hxW, hdim, he⟩ :=
    properCycle_geometric_face_cofinal_charts K hK V hV s hs x hx P hxP
  refine ⟨W, hWP, hxW, ?_⟩
  intro j hj
  let w : W := ⟨x, hxW⟩
  have hy : (e w).2 = y := (he w).mp (intrinsicInterior_subset hx)
  letI : T1Space (properCycle_log_tangent a × Y) := e.t1Space
  letI : T1Space Y := t1Space_of_injective_of_continuous
    (f := fun y : Y => ((0 : properCycle_log_tangent a), y))
    (fun b c h => congrArg Prod.snd h) (continuous_const.prodMk continuous_id)
  have hnormal : Subsingleton (orientationGroup Y j y) := by
    rw [← hy]
    exact properCycle_real_chart_normal_homology_subsingleton (TopCat.of K.space) W
      (properCycle_log_tangent a) Y e w j
      (hvan (j + Module.finrank ℝ (properCycle_log_tangent a)) (by omega))
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (properCycle_product_chart_support_subsingleton (TopCat.of K.space)
      {z : K.space | z.val ∈ convexHull ℝ (s : Set E)} W
      (properCycle_log_tangent a) Y y e he j hnormal)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A dimension skeleton locally equals the given open face, so its supported groups vanish in the ambient range.
Source: Munkres, Elements of Algebraic Topology, section 2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_skeleton_cofinal_vanishing_at_point {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ)
    (s : Finset E) (hs : s ∈ D.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hvan : ∀ j : ℕ, j ≠ N →
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (n : ℕ) (hbound : n + s.card ≤ N) (P : Opens K.space) (hxP : x ∈ P) :
    ∃ W : Opens K.space, W ≤ P ∧ x ∈ W ∧ ∀ j : ℕ, j ≤ n →
      IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set K.space)
          {z : K.space | ∃ q ∈ D.faces, q.card ≤ s.card ∧
            z.val ∈ convexHull ℝ (q : Set E)}) j) := by
  classical
  obtain ⟨O, hxO, hO⟩ := properCycle_geometric_face_incidence_neighborhood K hK s (hDK hs) x hx
  obtain ⟨W, hWP, hxW, hzero⟩ := properCycle_geometric_face_cofinal_vanishing_at_point
    K hK V hV N s (hDK hs) x hx hvan n hbound (P ⊓ O) ⟨hxP, hxO⟩
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
