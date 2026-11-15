import HodgeLean.Foundations.Program.G32Native.CanonicalNormalThomTransport

/-! # The analytic normal Euler input of U13 -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle
open HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Analytic normal Euler localized in the same coefficient-model support as U13.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom naturality
and the zero-section definition of Euler. -/
theorem canonicalNormalEuler_model
    (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G)
    [CompactSpace (ComplexPoint G.Q)] [T2Space (ComplexPoint G.Q)]
    [IsIntegral (s2c_subscheme G.Q
      ((s2e_s2b_intersectionIdeal G.k (Finset.univ.erase 0)).comap G.eQ.hom.left)).left] :
    i1_normalBundleEuler G.ι.left G.k G.W.hom (Over.w G.ι) =
    s2e_classToAbsolute G.Q (s2e_componentCycle (s2c_subschemeι G.Q
      ((s2e_s2b_intersectionIdeal G.k (Finset.univ.erase 0)).comap G.eQ.hom.left)) ℚ) G.k
      (relativeCohomologyMap ℚ (2 * G.k) (normalComponentPointPairIso G.k G.eQ).inv
        (relativeCohomologyMap ℚ (2 * G.k) (projectiveNormalSectionPairMap G.k)
          (normalKernelGlobalThomClass G.k))) := by
  letI (x : ComplexPoint G.Q) := i1_normalFibreTopology G.ι.left x
  letI := i1_normalTotalTopology G.ι.left G.k
  let N := i1_analyticNormal G.ι.left G.k G.W.hom (Over.w G.ι)
  letI := N.fiberBundle
  letI := N.vectorBundle
  obtain ⟨F, hzero, hcoeff, hclass⟩ :=
    canonical_coefficient_thom_transport_aux G D
  rw [← normalEulerModel_localization G.k G.eQ]
  have hsquare :
      TopCat.ofHom (i1_zeroSection G.k (i1_normalFibre G.ι.left)) ≫ TopPair.Hom.fst F =
      TopPair.Hom.fst (normalComponentPointPairIso G.k G.eQ).inv ≫
        TopCat.ofHom (projectiveNormalZeroSection G.k) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact hzero x
  exact bundleEuler_of_supported_pullback G.k (i1_normalFibre G.ι.left) F
    (TopPair.Hom.fst (normalComponentPointPairIso G.k G.eQ).inv)
    (TopCat.ofHom (projectiveNormalZeroSection G.k))
    (normalKernelGlobalThomClass G.k) hsquare hclass

/-- Exact U13 comparison, retaining the U12 analytic self-restriction input. -/
theorem canonicalNormalEuler_comparison
    (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G) [IsIntegral G.Q.left]
    [CompactSpace (ComplexPoint G.Q)] [T2Space (ComplexPoint G.Q)]
    (c : s2e_supportedClass G.W (s2e_componentCycle G.ι ℚ) G.k)
    (hself : s2e_normalEuler G.ι G.k c =
      i1_normalBundleEuler G.ι.left G.k G.W.hom (Over.w G.ι)) :
    ∀ (hpt : IsIntegral (s2c_subscheme G.Q
      ((s2e_s2b_intersectionIdeal G.k (Finset.univ.erase 0)).comap G.eQ.hom.left)).left),
      letI := hpt
      s2e_normalEuler G.ι G.k c =
      s2e_classToAbsolute G.Q (s2e_componentCycle (s2c_subschemeι G.Q
        ((s2e_s2b_intersectionIdeal G.k (Finset.univ.erase 0)).comap G.eQ.hom.left)) ℚ) G.k
        (relativeCohomologyMap ℚ (2 * G.k) (normalComponentPointPairIso G.k G.eQ).inv
          (relativeCohomologyMap ℚ (2 * G.k) (projectiveNormalSectionPairMap G.k)
            (normalKernelGlobalThomClass G.k))) := by
  intro hpt
  letI := hpt
  exact hself.trans (canonicalNormalEuler_model G D)

#print axioms canonicalNormalEuler_model
#print axioms canonicalNormalEuler_comparison
end HodgeLean.Foundations.Program.G32Native
