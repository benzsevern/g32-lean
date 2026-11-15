import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCofinalChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealChartNormal
import HodgeLean.Foundations.QuotientDuality.ProperCycleProductPurity

/-! # Actual local support vanishing along finite geometric face interiors -/

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
lemma properCycle_geometric_face_cofinal_vanishing {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space,
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
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
      (hvan (j + Module.finrank ℝ (properCycle_log_tangent a)) (by omega) x)
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (properCycle_product_chart_support_subsingleton (TopCat.of K.space)
      {z : K.space | z.val ∈ convexHull ℝ (s : Set E)} W
      (properCycle_log_tangent a) Y y e he j hnormal)

end HodgeLean.Foundations.QuotientDuality
