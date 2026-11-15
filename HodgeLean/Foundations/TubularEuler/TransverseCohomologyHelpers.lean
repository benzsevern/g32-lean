import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Local cohomology action of an invertible complex derivative

The supplied nonlinear normal coordinate retains coefficient one after restriction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.TubularEuler

theorem complexDerivative_local_relativeCohomologyMap (k : ℕ)
    (U : Set (Fin k → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (f : (Fin k → ℂ) → (Fin k → ℂ)) (hf : ContinuousOn f U) (hf0 : f 0 = 0)
    (D : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ))
    (hD : HasFDerivAt f D.toContinuousLinearMap 0) :
    ∃ (V : Set (Fin k → ℂ)) (hVU : V ⊆ U)
      (hne : ∀ w, w ∈ V → w ≠ 0 → f w ≠ 0),
      IsOpen V ∧ 0 ∈ V ∧
      relativeCohomologyMap ℚ (2 * k)
        (complexNeighborhoodPuncturedPairMapOf k V f (hf.mono hVU) hne) =
      relativeCohomologyMap ℚ (2 * k) (neighborhoodPointComplementPairMap V 0) := by
  let A := complexMatrixOfContinuousLinearMap k D.toContinuousLinearMap
  have hA : A.det ≠ 0 := complexMatrixOfContinuousLinearMap_det_ne_zero k
    D.toContinuousLinearMap D.injective
  have hAD : (A.mulVecLin.toContinuousLinearMap :
      (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) = D.toContinuousLinearMap :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec k D.toContinuousLinearMap)
  obtain ⟨V, hVU, hne, hVo, h0V, hclass⟩ :=
    exists_open_complexDifferentiable_localClass_invariance k A hA U hU h0U f hf hf0
      (by rw [hAD]; exact hD)
  let i := neighborhoodPointComplementPairMap V 0
  let g := complexNeighborhoodPuncturedPairMapOf k V f (hf.mono hVU) hne
  have hi := neighborhoodPointComplement_relativeHomologyMap_bijective V 0 hVo h0V (2 * k)
  obtain ⟨u, hu⟩ := hi.2 (standardComplexLocalClass ℚ k)
  have hlinear (w : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * k)) :
      relativeHomologyMap ℚ (2 * k) g w = relativeHomologyMap ℚ (2 * k) i w := by
    have hg := (Submodule.span_singleton_eq_top_iff ℚ
      (standardComplexLocalClass ℚ k)).mp (span_standardComplexLocalClass_eq_top_for_chart k)
    obtain ⟨r, hr⟩ := hg (relativeHomologyMap ℚ (2 * k) i w)
    have hw : r • u = w := hi.1 (by rw [map_smul, hu]; exact hr)
    rw [← hw, map_smul, map_smul, hu, hclass u hu]
  refine ⟨V, hVU, hne, hVo, h0V, ?_⟩
  apply LinearMap.ext
  intro α
  apply (relativeCohomologyEquivDualHomology ℚ _ (2 * k)).injective
  apply LinearMap.ext
  intro w
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  exact congrArg (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ k) (2 * k) α)
    (hlinear w)

#print axioms complexDerivative_local_relativeCohomologyMap

end HodgeLean.Foundations.TubularEuler
