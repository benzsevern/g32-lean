import HodgeLean.Foundations.Program.RelativeFrameOperatorMeromorphicGlue

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_centered_chart_expression {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (p : X) (hp : p ∈ e.source) (hUp : e p ∈ U)
    (hlocal : ∀ q ∈ e.source, e q ∈ U → ∀ v : TangentSpace 𝓘(ℂ, ℂ) q,
      θ ⟨q, v⟩ = f (e q) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e q v)) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ψ 0 = e p ∧ deriv ψ 0 ≠ 0 ∧
      HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p =ᶠ[𝓝 0]
        (fun z ↦ f (ψ z) * deriv ψ z) := by
  let a := chartAt ℂ p
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  let A : ℂ → ℂ := fun z ↦ a p + L z
  let t : ℂ → ℂ := e ∘ a.symm
  let ψ : ℂ → ℂ := t ∘ A
  have haMem : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X := IsManifold.chart_mem_maximalAtlas p
  have hpa : p ∈ a.source := mem_chart_source ℂ p
  have hapt : a p ∈ a.target := a.map_source hpa
  have hA0 : A 0 = a p := by simp [A]
  have ht : AnalyticAt ℂ t (a p) := rf4_atlas_transition_analytic a e
    haMem he (a p) hapt (by rwa [a.left_inv hpa])
  have hAan : AnalyticAt ℂ A 0 := analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0)
  have hψ : AnalyticAt ℂ ψ 0 := by
    exact (hA0 ▸ ht).comp hAan
  have hψ0 : ψ 0 = e p := by simp only [ψ, Function.comp_apply, hA0, t, a.left_inv hpa]
  have hAder (z : ℂ) : HasDerivAt A (L 1) z :=
    L.toContinuousLinearMap.hasDerivAt.const_add _
  have hψder0 : deriv ψ 0 = deriv t (a p) * L 1 := by
    have hd := (hA0 ▸ ht.differentiableAt.hasDerivAt).comp 0 (hAder 0)
    simpa only [ψ, hA0] using hd.deriv
  have hprod := rf4_atlas_transition_deriv a e a haMem he
    haMem (a p) hapt (by rwa [a.left_inv hpa])
      (by rw [a.left_inv hpa]; exact hpa)
  rw [rf4_atlas_inverse_deriv a (a p) hapt] at hprod
  have htne : deriv t (a p) ≠ 0 := by
    intro h
    change deriv (e ∘ a.symm) (a p) = 0 at h
    rw [h, mul_zero] at hprod
    exact one_ne_zero hprod
  have hL : L 1 ≠ 0 := by
    intro h
    exact one_ne_zero (L.injective (h.trans L.map_zero.symm))
  refine ⟨ψ, hψ, hψ0, hψder0 ▸ mul_ne_zero htne hL, ?_⟩
  have hV := a.isOpen_inter_preimage_symm (e.isOpen_inter_preimage hU)
  have hpV : a p ∈ a.target ∩ a.symm ⁻¹' (e.source ∩ e ⁻¹' U) := by
    refine ⟨hapt, ?_⟩
    change a.symm (a p) ∈ e.source ∧ e (a.symm (a p)) ∈ U
    rw [a.left_inv hpa]
    exact ⟨hp, hUp⟩
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), A z ∈ a.target ∩ a.symm ⁻¹' (e.source ∩ e ⁻¹' U) :=
    hAan.continuousAt.preimage_mem_nhds (by rw [hA0]; exact hV.mem_nhds hpV)
  filter_upwards [hev] with z hz
  have htz := rf4_atlas_transition_analytic a e haMem he
    (A z) hz.1 hz.2.1
  have heD := (contMDiffAt_of_mem_maximalAtlas he hz.2.1).mdifferentiableAt (by simp)
  have haD := (contMDiffAt_symm_of_mem_maximalAtlas haMem
    hz.1).mdifferentiableAt (by simp)
  have hchain := congrArg (fun B : ℂ →L[ℂ] ℂ ↦ B (L 1)) (mfderiv_comp (A z) heD haD)
  rw [mfderiv_eq_fderiv] at hchain
  change fderiv ℂ (e ∘ a.symm) (A z) (L 1) =
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (a.symm (A z))
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a.symm (A z) (L 1)) at hchain
  rw [fderiv_eq_deriv_mul] at hchain
  have hψder : deriv ψ z = deriv t (A z) * L 1 :=
    (htz.differentiableAt.hasDerivAt.comp z (hAder z)).deriv
  change θ ⟨a.symm (A z), b4cov_vec p (a.symm (A z)) (L 1)⟩ = _
  have hvec : (⟨a.symm (A z), b4cov_vec p (a.symm (A z)) (L 1)⟩ :
      TangentBundle 𝓘(ℂ, ℂ) X) =
      ⟨a.symm (A z), mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a.symm (A z) (L 1)⟩ := by
    rw [b4c_residue_vec_chart hz.1]
    exact (rf2_inverse_chart_vector X p ⟨A z, hz.1⟩ (L 1)).symm
  rw [hvec, hlocal _ hz.2.1 hz.2.2]
  rw [← hchain, ← hψder]
  rfl

end HodgeLean.Foundations.Program
