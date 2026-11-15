import HodgeLean.Foundations.Program.G32Native.ProjectiveKernelBundleThomNaturality
import HodgeLean.Foundations.Program.G32Native.PairedConormalAnalyticKernelIdentification
import HodgeLean.Foundations.Program.G32Native.NormalizedThomPullback
import HodgeLean.Foundations.Program.G32Native.NormalEulerModelLocalization

/-! # Euler class of an elementary projective conormal modification -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Comparison of the dual of an elementary projective conormal
modification with the normalized projective evaluation-kernel model.
The right side is the localization of the model's actual Thom coclass;
no hyperplane coclass or signed-power identity is an input.
Source: Hartshorne, Algebraic Geometry, II.8, Euler sequence;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.6, pp. 16–17;
Bott–Tu, Differential Forms in Algebraic Topology, §20, top Chern and Euler.
This step requires a comparison for the supplied sheaf sequence, not just
its numerical ranks or its formal inverse polynomial. -/
theorem paired_conormal_model_comparison_aux
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (V : Scheme) (j : Q.left ⟶ V) [IsClosedImmersion j]
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV]
    [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (M : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (E : s2c_conormal j ≅ (Scheme.Modules.pullback eQ.hom.left).obj M)
    (f : (SheafOfModules.free
      (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin k) :
        (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M)
    (g : M ⟶ (Scheme.Modules.pushforward
      (s2c_subschemeι (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left).obj
      (SheafOfModules.unit (s2c_subscheme
        (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left.ringCatSheaf))
    (hfg : f ≫ g = 0) (hseq : (ShortComplex.mk f g hfg).ShortExact) :
    i1_normalBundleEuler j k sV hj =
      s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (relativeCohomologyMap ℚ (2 * k) (EulerModel.normalComponentPointPairIso k eQ).inv
          (relativeCohomologyMap ℚ (2 * k) (EulerModel.projectiveNormalSectionPairMap k)
            (EulerModel.normalKernelGlobalThomClass k))) := by
  letI (x : ComplexPoint Q) := i1_normalFibreTopology j x
  letI := i1_normalTotalTopology j k
  let N := i1_analyticNormal j k sV hj
  letI := N.fiberBundle
  letI := N.vectorBundle
  obtain ⟨D, hbase⟩ := paired_conormal_analytic_kernel_identification_aux
    Q k hk eQ V j sV hj M E f g hfg hseq
  rw [← normalEulerModel_localization k eQ]
  have hsquare :
      TopCat.ofHom (i1_zeroSection k (i1_normalFibre j)) ≫ TopPair.Hom.fst D.pairMap =
        TopPair.Hom.fst (EulerModel.normalComponentPointPairIso k eQ).inv ≫
          TopCat.ofHom (EulerModel.projectiveNormalZeroSection k) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change TopPair.Hom.fst D.pairMap (i1_zeroSection k (i1_normalFibre j) x) =
      EulerModel.projectiveNormalZeroSection k ((EulerModel.normalComponentHomeomorph k eQ).symm x)
    rw [D.zeroSection, hbase]
  exact bundleEuler_of_supported_pullback k (i1_normalFibre j) D.pairMap
    (TopPair.Hom.fst (EulerModel.normalComponentPointPairIso k eQ).inv)
    (TopCat.ofHom (EulerModel.projectiveNormalZeroSection k))
    (EulerModel.normalKernelGlobalThomClass k) hsquare
    (projective_kernel_bundle_thom_naturality_aux k (i1_normalFibre j) D)

#print axioms paired_conormal_model_comparison_aux
end HodgeLean.Foundations.Program.G32Native
