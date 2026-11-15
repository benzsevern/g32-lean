import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartClass
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChartGenerator
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartPointClassNormalization

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A coordinate class with integral multiplicity maps under the inverse
chart to the same multiple of its chart-local class. -/
theorem s2v_l1b_action_chart_inverse_class_smul
    (R : Type) [CommRing R] {M : Type} [TopologicalSpace M]
    (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ))
    (x : M) (hx : x ∈ e.source) (P : TopPair)
    (A : P ⟶ neighborhoodPointComplementPair e.target (e x))
    (a : RelativeHomology R P (2 * d)) (k : ℤ)
    (ha : relativeHomologyMap R (2 * d)
      (A ≫ neighborhoodPointComplementPairMap e.target (e x)) a =
        k • relativeHomologyMap R (2 * d)
          (translationPointComplementPairMap (Fin d → ℂ) (e x))
            (standardComplexLocalClass R d)) :
    relativeHomologyMap R (2 * d) (A ≫ chartTargetInverseAtSourcePairMap d e x) a =
      k • b6m_localClassOfChart R d e x hx := by
  let Q := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
    (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have hAQ : relativeHomologyMap R (2 * d) A a =
      k • relativeHomologyMap R (2 * d) Q (standardComplexLocalClass R d) := by
    apply (b6m_point_excision_bijective R e.target (e x)
      e.open_target (e.map_source hx) (2 * d)).1
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ha, map_zsmul]
    exact congrArg (fun b => k • b) (b6m_radialTargetPointPairMap_normalization R d e.target (e x)
      (chartRadius d e x hx) (chartRadius_pos d e x hx)
      (ball_chartRadius_subset d e x hx) 0 (e x)
      (OpenPartialHomeomorph.univBall_apply_zero _ _)).symm
  rw [relativeHomologyMap_comp, LinearMap.comp_apply, hAQ, map_zsmul,
    ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  congr 1
  rw [show Q ≫ chartTargetInverseAtSourcePairMap d e x = chartModelEmbeddingPair d e x hx
    from radialTargetPointPairMap_chartTargetInverseAtSource d e x hx]
  rfl

end HodgeLean.Foundations.Program
