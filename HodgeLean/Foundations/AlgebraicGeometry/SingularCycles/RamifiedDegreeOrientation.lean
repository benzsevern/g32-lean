import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeAnalytic
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! # Orientation agreement for supplied holomorphic point charts

Both transition maps are analytic. The chart orientation comparison then
identifies their exact normalized local classes.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem holomorphic_point_chart_orientation_independent
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ)
    (e e' : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (he' : a3b4_IsHolChart X.hom e')
    (x : ComplexPoint X) (hx : x ∈ (pointChart e).source) (hx' : x ∈ (pointChart e').source) :
    localClassOfChart d (pointChart e) x hx = localClassOfChart d (pointChart e') x hx' := by
  apply localClassOfChart_eq_of_analyticAt_transition
  · have h := map_in_pointChart_analytic (𝟙 X) d e e' he he'
      (pointChart e x) ((pointChart e).map_source hx) (by
        rw [Point.map_id, (pointChart e).left_inv hx]
        exact hx'.1)
    simpa only [Point.map_id] using h
  · have h := map_in_pointChart_analytic (𝟙 X) d e' e he' he
      (pointChart e' x) ((pointChart e').map_source hx') (by
        rw [Point.map_id, (pointChart e').left_inv hx']
        exact hx.1)
    simpa only [Point.map_id] using h

theorem holomorphic_neighborhood_orientation_independent
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [T1Space (ComplexPoint X)] (d : ℕ)
    (e e' : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (he' : a3b4_IsHolChart X.hom e')
    (x : ComplexPoint X) (hx : x ∈ (pointChart e).source) (hx' : x ∈ (pointChart e').source)
    (U : Set (ComplexPoint X)) (hU : IsOpen U) (hxU : x ∈ U) :
    neighborhoodOrientation d (pointChart e) x hx U hU hxU =
      neighborhoodOrientation d (pointChart e') x hx' U hU hxU := by
  unfold neighborhoodOrientation
  rw [holomorphic_point_chart_orientation_independent X d e e' he he' x hx hx']

end AlgebraicGeometry.SingularCycles
