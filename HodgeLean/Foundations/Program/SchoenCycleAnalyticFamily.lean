import HodgeLean.Foundations.Program.SchoenCycleMeromorphicBounds
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-! # Local analytic families after removing fixed poles
A common simple pole can be removed before the coefficients vary.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Multiplication by the local parameter removes a pole of order at most one. -/
theorem s2e_simple_pole_analytic_extension (f : ℂ → ℂ)
    (hf : MeromorphicAt f 0) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ (fun z => z * f z) =ᶠ[𝓝[≠] 0] g := by
  have hm : MeromorphicAt (fun z => z * f z) 0 := analyticAt_id.meromorphicAt.mul hf
  apply hm.meromorphicOrderAt_nonneg_iff.mp
  change 0 ≤ meromorphicOrderAt (id * f) 0
  rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hf]
  change 0 ≤ meromorphicOrderAt id 0 + meromorphicOrderAt f 0
  rw [meromorphicOrderAt_id]
  have hh := add_le_add_left ho (1 : WithTop ℤ)
  simpa [add_comm] using hh

end HodgeLean.Foundations.Program
