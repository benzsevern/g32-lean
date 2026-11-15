import HodgeLean.Foundations.Program.G32Native.CanonicalSignedEuler

/-! # The coefficient zero-section expression on the retained component -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Localization of the model Euler operation uses the original projective coordinates.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, zero-section pullback
and homotopy of sections; Hatcher, Algebraic Topology, §3.1, relative naturality. -/
theorem normalEulerModel_localization
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    cohomologyMap ℚ (2 * k)
      (TopPair.Hom.fst (normalComponentPointPairIso k eQ).inv)
      (cohomologyMap ℚ (2 * k) (TopCat.ofHom (projectiveNormalZeroSection k))
        (forgetSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
          {w | w.1.2 = 0} (2 * k) (normalKernelGlobalThomClass k))) =
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
      (relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
        (relativeCohomologyMap ℚ (2 * k) (projectiveNormalSectionPairMap k)
          (normalKernelGlobalThomClass k))) := by
  rw [projectiveNormalZeroSection_localization]
  exact (RelativeTrace.forget_naturality (normalComponentPointPairIso k eQ).inv
    (2 * k) (relativeCohomologyMap ℚ (2 * k) (projectiveNormalSectionPairMap k)
      (normalKernelGlobalThomClass k))).symm

#print axioms normalEulerModel_localization
end HodgeLean.Foundations.Program.G32Native
