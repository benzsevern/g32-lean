import HodgeLean.Foundations.Program.SchoenTransferQ3ActualSliceCharts
import HodgeLean.Foundations.Program.SchoenTransferQ3NormalCoclassGeneration

/-! The actual singleton support of a centred zero-tangential chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- In a centred point chart, zero normal coordinates identify exactly the
marked point, with no additional support assumption. -/
theorem s4_q3_zero_tangent_chart_flattens_point
    {M : Type} [TopologicalSpace M] (c : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0) :
    ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0 := by
  intro y hy
  constructor
  · intro h
    rcases Set.mem_singleton_iff.mp h with rfl
    exact congrArg Prod.snd he
  · intro h
    apply Set.mem_singleton_iff.mpr
    apply e.injOn hy hx
    apply Prod.ext (Subsingleton.elim _ _) (h.trans (congrArg Prod.snd he).symm)

end HodgeLean.Foundations.Program
