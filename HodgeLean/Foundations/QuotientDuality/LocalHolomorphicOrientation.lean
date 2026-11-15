import HodgeLean.Foundations.QuotientDuality.LocalOpenHolomorphicCharts
import HodgeLean.Foundations.QuotientDuality.LocalOrientationPropagation

/-! Holomorphic chart normalization transports local orientations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem localOrientation_preserved_at_holomorphic_chart
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (d : ℕ)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (hnorm : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      o.generator x = localClassOfChart d E x hx)
    (H : ComplexPoint X ≃ₜ ComplexPoint X)
    (hH : an_IsHom (f4_analytification X) (f4_analytification X) H.symm)
    (x : ComplexPoint X) (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (hx : x ∈ E.source)
    (hE : ∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) :
    relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H x)
      (o.generator x) = o.generator (H x) := by
  rw [hnorm x E hx hE, localClassOfChart_homeomorphTransport]
  symm
  apply hnorm
  intro i
  exact hH.2 E.source E.open_source (fun y => E y i) (hE i)

#print axioms localOrientation_preserved_at_holomorphic_chart
end HodgeLean.Foundations.QuotientDuality
