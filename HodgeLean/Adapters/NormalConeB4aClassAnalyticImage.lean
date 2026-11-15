import HodgeLean.Adapters.NormalConeB4aClassAnalyticChartMap

/-! # Local equations for images under analytic charts

Route: the finite mapping theorem applies to the proper holomorphic map
between chart domains. Transfer its local equations from the target open
space to the ambient complex coordinate space.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Topology
open HodgeLean.Foundations.Analytic

/-- The image of an analytic subset under an analytic chart has local
analytic equations in the target coordinate space. -/
theorem a3b4a_classAnalyticChart_image_localEquations
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source) (A : Set e.source)
    (hA : an_IsClosedAnalytic (anrem_openSpace (an_euclidSpace n) e.open_source) A)
    (y : e.target) (hy : y ∈ e.toHomeomorphSourceTarget '' A) :
    anrem_LocEq (Subtype.val '' (e.toHomeomorphSourceTarget '' A)) y.1 := by
  have hfin (w : e.target) : (A ∩ e.toHomeomorphSourceTarget ⁻¹' {w}).Finite := by
    apply Set.Subsingleton.finite
    intro x hx z hz
    exact e.toHomeomorphSourceTarget.injective (hx.2.trans hz.2.symm)
  have himage := an_finite_mapping
    (anrem_openSpace (an_euclidSpace n) e.open_source)
    (anrem_openSpace (an_euclidSpace m) e.open_target)
    e.toHomeomorphSourceTarget (a3b4a_classAnalyticChart_isProperHom e ha) hA hfin
  have hnear := (anrem_anNear_openSpace_iff (an_euclidSpace m) e.open_target
    (e.toHomeomorphSourceTarget '' A) y).mp (himage.2 y hy)
  have hloc := anrem_anNear_chart (an_euclidSpace m) hnear PUnit.unit (mem_univ _)
  change anrem_LocEq (id '' (Subtype.val '' (e.toHomeomorphSourceTarget '' A) ∩ univ)) y.1 at hloc
  simpa only [Set.inter_univ, Set.image_id] using hloc

end HodgeLean.Adapters
