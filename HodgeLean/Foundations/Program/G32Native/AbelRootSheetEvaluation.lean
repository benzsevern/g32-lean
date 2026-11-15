import HodgeLean.Foundations.Program.G32Native.AbelSheetInverse

/-! # Exact evaluation of coefficient lifts on original root tuples -/
noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program.G32Native
variable {R V X Y : Type*} [TopologicalSpace R] [TopologicalSpace V]
  [TopologicalSpace X] [TopologicalSpace Y] [Zero R] [Zero V]

/-- A sheet lift of exact coefficient values evaluates to the original root tuple image. -/
theorem root_sheet_evaluation (f : X → Y) (e : OpenPartialHomeomorph Y V)
    (s : V → X) (c : R → V) (r : R → Y)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hr : ContinuousAt r 0)
    (hrsource : r 0 ∈ e.source)
    (hs : ∀ᶠ v in 𝓝 (0 : V), f (s v) = e.symm v)
    (he : ∀ᶠ z in 𝓝 (0 : R), e (r z) = c z) :
    ∀ᶠ z in 𝓝 (0 : R), f (s (c z)) = r z := by
  have ht : Tendsto c (𝓝 0) (𝓝 (0 : V)) := by simpa only [hc0] using hc.tendsto
  filter_upwards [ht.eventually hs, he, hr (e.open_source.mem_nhds hrsource)] with z hz hez hrz
  exact hz.trans ((congrArg e.symm hez).symm.trans (e.left_inv hrz))

#print axioms root_sheet_evaluation
end HodgeLean.Foundations.Program.G32Native
