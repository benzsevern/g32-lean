import HodgeLean.Foundations.Connected
import HodgeLean.RealDefs.DegreeZero

/-!
# Discharging complex-point preconnectedness

HC: no distance. AV milestone: no distance. The stated connectedness input is now proved.
-/

namespace HodgeLean.Adapters

/-- Retires the stated hypothesis `ComplexPointsPreconnected` for every smooth integral
projective `X` it quantifies over. The ledger records this proof as an unconditional milestone;
older milestone signatures retain their explicit argument.

Source: upstream `Other/AlgebraicGeometry/ComplexPoint/SmoothConnected.lean` at `2ead713`,
`AlgebraicGeometry.ComplexPoint.connectedSpace`. -/
@[hodge_milestone]
theorem complexPointsPreconnected : HodgeLean.RealDefs.ComplexPointsPreconnected := by
  constructor
  intro X _ _ _
  let := HodgeLean.Foundations.pathConnectedSpace_complexPoint X
  infer_instance

end HodgeLean.Adapters

#print axioms HodgeLean.Adapters.complexPointsPreconnected
