import HodgeLean.Foundations.Program.RelativeFrameOperatorCentered

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open TauCeti.Contour
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_chartField_meromorphic {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (p : X) (hp : p ∈ e.source) (hUp : e p ∈ U)
    (hlocal : ∀ q ∈ e.source, e q ∈ U → ∀ v : TangentSpace 𝓘(ℂ, ℂ) q,
      θ ⟨q, v⟩ = f (e q) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e q v)) (hf : MeromorphicAt f (e p)) :
    MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 := by
  obtain ⟨ψ, hψ, hψ0, _, heq⟩ := rf4_centered_chart_expression θ e he U hU f p hp hUp hlocal
  have hfψ : MeromorphicAt f (ψ 0) := by rwa [hψ0]
  apply MeromorphicAt.congr ((hfψ.comp_analyticAt hψ).fun_mul hψ.deriv.meromorphicAt)
  exact (heq.filter_mono nhdsWithin_le_nhds).symm

theorem rf4_chartField_residue_hol {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (p : X) (hp : p ∈ e.source) (hUp : e p ∈ U)
    (hlocal : ∀ q ∈ e.source, e q ∈ U → ∀ v : TangentSpace 𝓘(ℂ, ℂ) q,
      θ ⟨q, v⟩ = f (e q) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e q v)) (hf : AnalyticAt ℂ f (e p)) :
    residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 0 := by
  obtain ⟨ψ, hψ, hψ0, _, heq⟩ := rf4_centered_chart_expression θ e he U hU f p hp hUp hlocal
  have hfψ : AnalyticAt ℂ f (ψ 0) := by rwa [hψ0]
  have han : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 :=
    ((hfψ.comp hψ).mul hψ.deriv).congr heq.symm
  exact residue_eq_zero_of_analyticAt han

theorem rf4_chartField_residue_simple {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (U : Set ℂ) (hU : IsOpen U) (β : ℂ → ℂ) (p : X) (hp : p ∈ e.source)
    (hUp : e p ∈ U) (hep : e p = 0) (hβ : AnalyticAt ℂ β 0)
    (hlocal : ∀ q ∈ e.source, e q ∈ U → ∀ v : TangentSpace 𝓘(ℂ, ℂ) q,
      θ ⟨q, v⟩ = (β (e q) + (e q)⁻¹) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e q v)) :
    residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 1 := by
  obtain ⟨ψ, hψ, hψ0, hψne, heq⟩ := rf4_centered_chart_expression θ e he U hU
    (fun w ↦ β w + w⁻¹) p hp hUp hlocal
  have hz : ψ 0 = 0 := hψ0.trans hep
  have hβψ : AnalyticAt ℂ β (ψ 0) := by rwa [hz]
  have hhol : AnalyticAt ℂ (fun z ↦ β (ψ z) * deriv ψ z) 0 := (hβψ.comp hψ).mul hψ.deriv
  have heq' : HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p =ᶠ[𝓝 0]
      (fun z ↦ β (ψ z) * deriv ψ z + deriv ψ z / ψ z) := by
    apply heq.trans
    exact Eventually.of_forall (fun z ↦ by simp only [div_eq_mul_inv]; ring)
  rw [residue_congr_nhdsNE (heq'.filter_mono nhdsWithin_le_nhds)]
  change residue ((fun z ↦ β (ψ z) * deriv ψ z) + (fun z ↦ deriv ψ z / ψ z)) 0 = 1
  rw [residue_add hhol.meromorphicAt (hψ.deriv.meromorphicAt.fun_div hψ.meromorphicAt),
    residue_eq_zero_of_analyticAt hhol,
    residue_div_of_zero_deriv_ne_zero hψ.deriv hψ hz hψne, div_self hψne, zero_add]

end HodgeLean.Foundations.Program
