import HodgeLean.Adapters.Connected

/-!
# The degree-zero case, with no hypotheses

`HodgeLean.RealDefs.hodge_degree_zero` (F-1658) proves the degree-zero case of upstream's Hodge
conjecture from a single stated hypothesis, `ComplexPointsPreconnected`. Torus stage S1 proved that
hypothesis (`HodgeLean.Adapters.complexPointsPreconnected`, from upstream's connectedness of
`X(ℂ)`). This file records the consequence: the degree-zero case holds with no hypotheses.

Relation to the goal: HC no distance (the degree-zero case is classical); AV milestone no distance.
It is the first result in this repository against upstream's real definitions that carries no
stated hypothesis.
-/

open CategoryTheory TopologicalSpace Opposite Limits AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.Adapters

/-- The codimension-zero cycle classes span `H^0(X(ℂ); ℚ)`, for every smooth projective integral
`X` over `ℂ`, with no hypotheses.

Source: `HodgeLean.RealDefs.algebraicCycleClassSpan_zero_eq_top` applied to
`complexPointsPreconnected`. -/
theorem algebraicCycleClassSpan_zero_eq_top_unconditional (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 0 = ⊤ :=
  HodgeLean.RealDefs.algebraicCycleClassSpan_zero_eq_top complexPointsPreconnected X

/-- **The degree-zero case of the Hodge conjecture, with no hypotheses.** For every smooth projective
integral `X` over `ℂ`, `Hdg^0(X; ℚ) ≤ algebraicCycleClassSpan X 0`, against upstream's (Paul-Lez)
definitions.

Source: Deligne, *The Hodge Conjecture* (Clay), statement with `p = 0`; the proof is
`HodgeLean.RealDefs.hodge_degree_zero` (F-1658) applied to `complexPointsPreconnected`.

Relation to the goal: HC no distance; AV milestone no distance.

Checks: F-1658 -/
@[hodge_milestone] theorem hodge_degree_zero_unconditional :
    ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      Hdg^0(X; ℚ) ≤ algebraicCycleClassSpan X 0 :=
  HodgeLean.RealDefs.hodge_degree_zero complexPointsPreconnected

end HodgeLean.Adapters

#print axioms HodgeLean.Adapters.hodge_degree_zero_unconditional
