import HodgeLean.Foundations.Curves.AbelTheorem.ConvexPrimitive

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem cutoff_form_primitive_on_chart (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h) (μ : C → ℝ)
    (hμ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ μ)
    (hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 → μ =ᶠ[𝓝 x] 0)
    (P : ℂ →L[ℝ] ℝ) (x : C) {U : Set E} (hUc : Convex ℝ U)
    (hUo : IsOpen U) (hU : U ⊆ (chartAt E x).target)
    (hone : ∀ u ∈ U, μ =ᶠ[𝓝 ((chartAt E x).symm u)] fun _ => 1) :
    ∃ f : E → ℝ, ∀ u ∈ U, HasFDerivAt f
      (b3Forms_toCLM (b3Forms_loc (b4c_residue_realForm h
        (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) P) x u)) u := by
  let α := b4c_residue_realForm h
    (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) P
  have hα : b3Forms_IsSmooth α := b4c_residue_smooth_global h w μ hμ hpoles P
  apply primitive_on_convex_domain (b3Forms_loc α x) hUc hUo ((hα x).mono hU)
  intro u hu
  rw [← b3Forms_loc_d hα x (hU hu)]
  have hd : b3Forms_d α ((chartAt E x).symm u) = 0 :=
    b4c_residue_d_eq_zero_of_constant h w μ hμ hpoles P (hone u hu)
  simp only [b3Forms_loc, hd]
  ext v
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
