import HodgeLean.Foundations.Program.SchoenTransferQ3TriangularCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Ambient charts adapted to an actual tangential map with the original normal coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.Program

/-- A tangential map invertible along a flattened support can replace the
old tangential coordinates while retaining all original normal coordinates. -/
theorem s4_q3_chart_adapted_to_tangential_map
    {M E F : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : OpenPartialHomeomorph M (E × F)) (x : M) (hx : x ∈ e.source)
    (hx0 : (e x).2 = 0) (G : M → E)
    (hG : AnalyticAt ℂ (fun v => G (e.symm v)) (e x))
    (hbij : Function.Bijective (fderiv ℂ (fun u => G (e.symm (u, 0))) (e x).1)) :
    ∃ d : OpenPartialHomeomorph M (E × F),
      x ∈ d.source ∧ d.source ⊆ e.source ∧
        ∀ y ∈ d.source, d y = (G y, (e y).2) := by
  let a := (e x).1
  have hcenter : e x = (a, 0) := Prod.ext rfl hx0
  rw [hcenter] at hG
  obtain ⟨Ψ, ha, hΨ, _, _⟩ := s4_q3_analytic_tangential_change_preserving_normals
    (fun v => G (e.symm v)) a hG hbij
  let d := e.trans Ψ
  have hxd : x ∈ d.source := by
    refine ⟨hx, ?_⟩
    change e x ∈ Ψ.source
    rw [hcenter]
    exact ha
  refine ⟨d, hxd, fun _ h => h.1, ?_⟩
  intro y hy
  change Ψ (e y) = _
  rw [hΨ, e.left_inv hy.1]

end HodgeLean.Foundations.Program
