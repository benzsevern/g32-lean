import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaFormEquivalence
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.SchemeFormReconstruction

/-! # Global scheme forms on the retained theta model

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- Global scheme forms on the retained model selected by the original curve-period coordinates.
Source: Birkenhake–Lange, §§1.1–1.2; Forster, §21; schemeFormHolEquiv.
HC no distance; AV milestone no distance. -/
def thetaSchemeFormEquiv (h : Module.finrank ℂ E = 1) :
    b3_HolForm E C ≃+ GlobalHolomorphicForm (model (C := C) h) 1 :=
  (thetaAnalyticFormEquiv h).toAddEquiv.trans (schemeFormHolEquiv (model (C := C) h)).symm

/-- The selected global scheme form has the original analytic invariant tangent values.
Source: Birkenhake–Lange, §§1.1–1.2; Forster, §21; thetaAnalyticFormEquiv_apply.
HC no distance; AV milestone no distance. -/
theorem thetaSchemeFormEquiv_values (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    schemeForm (model (C := C) h) (thetaSchemeFormEquiv h θ) = (thetaAnalyticForm h θ).val := by
  have he := congrArg Subtype.val
    ((schemeFormHolEquiv (model (C := C) h)).apply_symm_apply (thetaAnalyticFormEquiv h θ))
  exact he.trans (congrArg Subtype.val (thetaAnalyticFormEquiv_apply h θ))

#print axioms thetaSchemeFormEquiv
#print axioms thetaSchemeFormEquiv_values

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
