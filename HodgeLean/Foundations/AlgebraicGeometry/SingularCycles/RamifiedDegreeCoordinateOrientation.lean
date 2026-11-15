import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeLocal
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartPointClassNormalization

/-! # Reading coordinate generators through inverse charts

Excision detects a class in the chart target by its image in the ambient
coordinate space. The inverse chart sends the normalized coordinate class
to the specified chart orientation, preserving its rational coefficient.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem chart_inverse_on_coordinate_generator
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (w : RelativeHomology ℚ (neighborhoodPointComplementPair e.target (e x)) (2 * d))
    (a : ℚ)
    (hw : relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap e.target (e x)) w =
      a • HodgeLean.RealDefs.translatedStandardComplexLocalClass d (e x)) :
    relativeHomologyMap ℚ (2 * d) (chartTargetInverseAtSourcePairMap d e x) w =
      a • localClassOfChart d e x hx := by
  let Q := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
    (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have hQ : relativeHomologyMap ℚ (2 * d)
      (neighborhoodPointComplementPairMap e.target (e x))
      (relativeHomologyMap ℚ (2 * d) Q (standardComplexLocalClass ℚ d)) =
      HodgeLean.RealDefs.translatedStandardComplexLocalClass d (e x) := by
    exact radialTargetPointPairMap_normalization d e.target (e x) (chartRadius d e x hx)
      (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
      (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have hwQ : w = a • relativeHomologyMap ℚ (2 * d) Q (standardComplexLocalClass ℚ d) := by
    apply (neighborhoodPointComplement_relativeHomologyMap_bijective e.target (e x)
      e.open_target (e.map_source hx) (2 * d)).1
    rw [hw, map_smul, hQ]
  rw [hwQ, map_smul, ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  change a • relativeHomologyMap ℚ (2 * d)
    (Q ≫ chartTargetInverseAtSourcePairMap d e x) (standardComplexLocalClass ℚ d) = _
  rw [show Q ≫ chartTargetInverseAtSourcePairMap d e x = chartModelEmbeddingPair d e x hx
    from radialTargetPointPairMap_chartTargetInverseAtSource d e x hx]
  rfl

def centeredChartTargetPairMap
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + e x ∈ e.target) :
    neighborhoodPointComplementPair V 0 ⟶ neighborhoodPointComplementPair e.target (e x) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v => ⟨v.1 + e x, hV v.1 v.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun v => ⟨⟨v.1.1 + e x, hV v.1.1 v.1.2⟩, by
      intro h
      apply v.2
      exact add_right_cancel (h.trans (zero_add (e x)).symm)⟩, by fun_prop⟩)
    (by ext v; rfl)

def centeredChartPairMap
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + e x ∈ e.target) :
    neighborhoodPointComplementPair V 0 ⟶ pointComplementPair x :=
  centeredChartTargetPairMap d e x V hV ≫ chartTargetInverseAtSourcePairMap d e x

theorem centered_chart_generator
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (V : Set (Fin d → ℂ)) (hV : ∀ v ∈ V, v + e x ∈ e.target)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * d))
    (hz : relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) z =
      standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d) (centeredChartPairMap d e x V hV) z =
      localClassOfChart d e x hx := by
  let Q := centeredChartTargetPairMap d e x V hV
  have hcomp : Q ≫ neighborhoodPointComplementPairMap e.target (e x) =
      neighborhoodPointComplementPairMap V 0 ≫
        translationPointComplementPairMap (Fin d → ℂ) (e x) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext v <;> rfl
  have hw : relativeHomologyMap ℚ (2 * d)
      (neighborhoodPointComplementPairMap e.target (e x))
      (relativeHomologyMap ℚ (2 * d) Q z) =
      (1 : ℚ) • HodgeLean.RealDefs.translatedStandardComplexLocalClass d (e x) := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hcomp,
      relativeHomologyMap_comp, LinearMap.comp_apply, hz, one_smul]
    rfl
  change relativeHomologyMap ℚ (2 * d) (Q ≫ chartTargetInverseAtSourcePairMap d e x) z = _
  rw [relativeHomologyMap_comp, LinearMap.comp_apply]
  simpa only [one_smul] using chart_inverse_on_coordinate_generator d e x hx
    (relativeHomologyMap ℚ (2 * d) Q z) 1 hw

end AlgebraicGeometry.SingularCycles
