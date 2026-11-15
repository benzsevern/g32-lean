import HodgeLean.Foundations.QuotientDuality.PersistenceTensorDualInjection
import HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge.CohomologyNaturality
import HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge.CohomologyScalarExtension

/-! Faithful coefficient comparison on singular cohomology of arbitrary spaces. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_cohomology_baseChange_injective (X : TopCat) (n : ℕ) :
    Function.Injective (cohomologyBaseChange X n) := by
  let e := cohomologyEquivDualHomology ℚ X n
  have he : LinearMap.liftBaseChange ℂ
      (Module.Dual.baseChange ℂ ∘ₗ e.toLinearMap) =
      (LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ)).comp
        (e.baseChange ℚ ℂ _ _).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a c
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
      LinearEquiv.coe_baseChange, LinearMap.baseChange_tmul]
  intro x y h
  apply (e.baseChange ℚ ℂ _ _).injective
  apply persistence_tensor_dual_injective
  have hc := congrArg (cohomologyEquivDualHomology ℂ X n) h
  simp only [cohomologyBaseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at hc
  have hd := (Module.Dual.congr (complexHomologyEquivBaseChange X n)).injective hc
  exact (LinearMap.congr_fun he x).symm.trans (hd.trans (LinearMap.congr_fun he y))

lemma persistence_eigen_preimages_of_coefficient_comparison
    {K U V U' V' : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']
    (T : Module.End K U) (S : Module.End K V)
    (T' : Module.End K U') (S' : Module.End K V')
    (f : U →ₗ[K] V) (f' : U' →ₗ[K] V')
    (a : U →ₗ[K] U') (b : V →ₗ[K] V')
    (ha : Function.Bijective a) (hb : Function.Injective b)
    (hT : ∀ u, a (T u) = T' (a u))
    (hS : ∀ v, b (S v) = S' (b v))
    (hf : ∀ u, b (f u) = f' (a u))
    (ζ : K)
    (hl : ∀ v', S' v' = ζ • v' → ∃! u', T' u' = ζ • u' ∧ f' u' = v')
    (v : V) (hv : S v = ζ • v) :
    ∃! u, T u = ζ • u ∧ f u = v := by
  have hv' : S' (b v) = ζ • b v := by rw [← hS, hv, map_smul]
  obtain ⟨u', hu', hunique⟩ := hl (b v) hv'
  obtain ⟨u, hu⟩ := ha.surjective u'
  have hue : T u = ζ • u := by
    apply ha.injective
    rw [hT, hu, hu'.1, map_smul, hu]
  have huf : f u = v := by
    apply hb
    rw [hf, hu, hu'.2]
  refine ⟨u, ⟨hue, huf⟩, ?_⟩
  intro z hz
  apply ha.injective
  rw [hu]
  apply hunique
  constructor
  · rw [← hT, hz.1, map_smul]
  · rw [← hf, hz.2]

end HodgeLean.Foundations.QuotientDuality
