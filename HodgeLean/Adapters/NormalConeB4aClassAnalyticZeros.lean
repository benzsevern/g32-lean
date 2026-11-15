import HodgeLean.Adapters.NormalConeB4aClassAnalyticChartMap

/-! # Analytic zero sets inside Euclidean open spaces

Route: continuity makes the zero set relatively closed, and its single
analytic defining function is a section of the open space's holomorphic
function sheaf.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Topology
open HodgeLean.Foundations.Analytic

/-- The zero set of an analytic scalar function on an open domain is a closed
analytic subset of that analytic open space. -/
theorem a3b4a_classAnalytic_zeroSet_openSpace
    {n : ℕ} (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (δ : (Fin n → ℂ) → ℂ) (hδ : AnalyticOnNhd ℂ δ U) :
    an_IsClosedAnalytic (anrem_openSpace (an_euclidSpace n) hU)
      {x : U | δ x = 0} := by
  have hc : Continuous (fun x : U => δ x) := continuousOn_iff_continuous_restrict.mp hδ.continuousOn
  refine ⟨isClosed_eq hc continuous_const, ?_⟩
  intro x hx
  refine ⟨univ, isOpen_univ, mem_univ _, 1,
    fun _ y => δ y.1.1, ?_, ?_⟩
  · intro j y i hy
    refine ⟨univ, isOpen_univ, mem_univ _, δ, hδ y.1.1 y.1.2, ?_⟩
    intro z hz
    rfl
  · intro y
    exact ⟨fun h _ => h, fun h => h 0⟩

end HodgeLean.Adapters
