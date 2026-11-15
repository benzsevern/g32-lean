import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]

theorem arc_form_support_of_thickening (h : Module.finrank ℂ E = 1) (x : C)
    {ε : ℝ} (hε : 0 < ε) {c c' : ℝ → ℂ} (hc : Continuous c) (hc' : Continuous c')
    {a b : ℝ} (hab : a ≤ b) (U : Set E) (hU : U ⊆ (chartAt E x).target)
    (ht : ∀ z ∈ cthickening ε (c '' Icc a b), b3Rest_ζ h x z ∈ U) :
    tsupport (b3Rest_arcForm h x ε c c' a b) ⊆ (chartAt E x).symm '' U := by
  obtain ⟨_, hcompact, hs⟩ := b3Rest_arcField_props h x hε hc hc' hab
  have hst : tsupport (b3Rest_arcField h x ε c c' a b) ⊆ U := by
    rintro u hu
    obtain ⟨z, hz, rfl⟩ := hs hu
    exact ht z hz
  exact (b3Rest_tsupport_ofLoc x hcompact (hst.trans hU)).trans (image_mono hst)

end HodgeLean.Foundations.Curves.AbelTheorem
