import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCoordinates
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpace

/-! # Analytic chart maps as proper holomorphic maps of open spaces

Route: the chart is a homeomorphism between its source and target. Its
analytic coordinates satisfy the holomorphic-map criterion on the two
Euclidean open spaces. This permits the finite mapping theorem to be used
on analytic subsets of the chart source.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations.Analytic

/-- An analytic chart is a proper holomorphic map between the analytic open
spaces carried by its source and target. -/
theorem a3b4a_classAnalyticChart_isProperHom
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source) :
    an_IsProperHom (anrem_openSpace (an_euclidSpace n) e.open_source)
      (anrem_openSpace (an_euclidSpace m) e.open_target) e.toHomeomorphSourceTarget := by
  refine ⟨e.toHomeomorphSourceTarget.isProperMap, ?_⟩
  apply a3b4a_class_isHom_of_coordinate_functions
    (anrem_openSpace (an_euclidSpace n) e.open_source)
    (anrem_openSpace (an_euclidSpace m) e.open_target)
    e.toHomeomorphSourceTarget e.toHomeomorphSourceTarget.continuous
  intro j k x i hxi
  refine ⟨univ, isOpen_univ, mem_univ _, fun v : Fin n → ℂ => e v k, ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) k).analyticAt _).comp
      (ha x.1.1 x.1.2)
  · intro y hy
    rfl

end HodgeLean.Adapters
