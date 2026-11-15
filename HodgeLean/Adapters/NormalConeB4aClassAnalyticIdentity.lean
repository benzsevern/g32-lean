import HodgeLean.Adapters.NormalConeB4aClassRemovableSet

/-! # Identity principle for local component equations

Route: the interior of a locally analytic set is relatively closed in a
connected open domain, by the identity principle on small balls.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations.Analytic

/-- A relatively closed locally analytic subset of a connected open domain
that contains a nonempty open piece contains the entire domain. -/
theorem a3b4a_classAnalytic_subset_of_interior
    (n : ℕ) (V A : Set (Fin n → ℂ)) (hV : IsOpen V) (hconn : IsPreconnected V)
    (hclosed : closure A ∩ V ⊆ A)
    (hA : ∀ x ∈ V ∩ A, anrem_LocEq A x)
    (hinterior : (V ∩ interior A).Nonempty) : V ⊆ A := by
  apply Set.Subset.trans
    (hconn.subset_of_closure_inter_subset isOpen_interior hinterior ?_) interior_subset
  intro x hx
  have hxA : x ∈ A := hclosed ⟨closure_mono interior_subset hx.1, hx.2⟩
  obtain ⟨U, hU, hxU, k, f, hf, hEq⟩ := hA x ⟨hx.2, hxA⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter hV).mem_nhds ⟨hxU, hx.2⟩)
  have hBU : Metric.ball x r ⊆ U := fun _ h => (hball h).1
  obtain ⟨y, hyB, hyI⟩ := mem_closure_iff.mp hx.1 (Metric.ball x r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hzero (i : Fin k) : EqOn (f i) 0 (Metric.ball x r) := by
    apply ((hf i).mono hBU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x r).isPreconnected hyB
    filter_upwards [isOpen_interior.mem_nhds hyI, Metric.isOpen_ball.mem_nhds hyB] with z hzI hzB
    exact (hEq z (hBU hzB)).mp (interior_subset hzI) i
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) fun z hz =>
    (hEq z (hBU hz)).mpr fun i => hzero i hz

end HodgeLean.Adapters
