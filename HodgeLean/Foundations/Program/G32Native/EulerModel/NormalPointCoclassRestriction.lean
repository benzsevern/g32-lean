import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointChartInverse

/-! # Exact native local normalization of the actual coordinate-point coclass -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual chart normal projection followed by its original parameterization is the literal neighborhood inclusion. -/
theorem normalComponentPointChart_pair_factorization
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (W : Set (ComplexPoint Q)) (hW : W ⊆ (normalComponentPointChart k eQ).source) :
    chartNormalProjectionPair (Fin 0 → ℂ) k (normalComponentPointChart k eQ)
      (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ))
      (normalComponentPointChart_support k eQ) W hW ≫
        (normalProjectiveChartPair k ≫ (normalComponentPointPairIso k eQ).hom) =
    a3b4_neighborhoodPairMap W
      (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ)) := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact normalComponentPointChart_reconstruct k eQ x.1.1 (hW x.1.2)
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact normalComponentPointChart_reconstruct k eQ x.1 (hW x.2)

#print axioms normalComponentPointChart_pair_factorization
/-- The actual component point coclass restricts to the native chart coclass on every neighborhood in its source. -/
theorem normalComponentPointCoclass_neighborhood
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (W : Set (ComplexPoint Q)) (hW : W ⊆ (normalComponentPointChart k eQ).source) :
    relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap W (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ)))
      (normalComponentPointCoclass k eQ) =
    chartNormalProjectionCoclass (Fin 0 → ℂ) k (normalComponentPointChart k eQ)
      (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ))
      (normalComponentPointChart_support k eQ) W hW := by
  rw [← normalComponentPointChart_pair_factorization k eQ W hW,
    relativeCohomologyMap_comp, LinearMap.comp_apply]
  unfold chartNormalProjectionCoclass
  congr 1
  exact normalComponentPointCoclass_chart k eQ

#print axioms normalComponentPointCoclass_neighborhood
end HodgeLean.Foundations.Program.G32Native.EulerModel
