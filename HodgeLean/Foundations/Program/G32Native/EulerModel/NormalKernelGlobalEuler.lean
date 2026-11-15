import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLeadingThom
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelHyperplaneSign

/-! # The exact Euler calculation for the original global kernel Thom coclass -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual global section pulls the same global normalized kernel Thom coclass back to the exact signed original projective point coclass. -/
theorem normalKernelGlobalThomClass_section (k : ℕ) :
    relativeCohomologyMap ℚ (2 * k) (projectiveNormalSectionPairMap k)
      (normalKernelGlobalThomClass k) = (-1 : ℚ) ^ k • normalProjectivePointCoclass k := by
  rw [projectiveNormalSection_supported_reconstruction, normalKernelGlobalThomClass_chart]
  exact normalKernelLocalThomClass_global_sign k

#print axioms normalKernelGlobalThomClass_section
/-- Zero-section pullback of the actual globally normalized kernel Thom coclass is the exact signed absolute projective point class. -/
theorem normalKernelGlobalThomClass_zeroSection (k : ℕ) :
    cohomologyMap ℚ (2 * k) (TopCat.ofHom (projectiveNormalZeroSection k))
      (forgetSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}
        (2 * k) (normalKernelGlobalThomClass k)) =
    (-1 : ℚ) ^ k • relativeCohomologyToAbsolute ℚ _ (2 * k) (normalProjectivePointCoclass k) := by
  rw [projectiveNormalZeroSection_localization, normalKernelGlobalThomClass_section, map_smul]

#print axioms normalKernelGlobalThomClass_zeroSection
/-- The same actual globally normalized kernel Thom coclass gives the exact signed hyperplane top power on the supplied component with its same supplied hyperplane normalization. -/
theorem normalKernelGlobalThomClass_hyperplane_sign
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) :
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
          (relativeCohomologyMap ℚ (2 * k) (projectiveNormalSectionPairMap k)
            (normalKernelGlobalThomClass k))) =
      (-1 : ℚ) ^ k • s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
        (s2e_classToAbsolute Q
          (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k := by
  rw [normalKernelGlobalThomClass_section k, map_smul, map_smul]
  change (-1 : ℚ) ^ k • s2e_classToAbsolute Q _ k (normalComponentPointCoclass k eQ) = _
  rw [normalComponentPointCoclass_hyperplane_power Q k hk eQ cH hcH]


#print axioms normalKernelGlobalThomClass_hyperplane_sign
/-- Every specified original leading-chart kernel fibre retains the exact complex point normalization of the same global Thom coclass. -/
theorem normalKernelGlobalThomClass_fibre (k : ℕ) (z : Fin k → ℂ) :
    relativeCohomologyMap ℚ (2 * k)
      (normalKernelLocalFibreInclusion k z ≫ normalKernelChartInclusionPair k)
      (normalKernelGlobalThomClass k) = normalizedPointCoclass k := by
  rw [relativeCohomologyMap_comp, LinearMap.comp_apply, normalKernelGlobalThomClass_chart]
  exact normalKernelLocalThomClass_fibre k z

#print axioms normalKernelGlobalThomClass_fibre
end HodgeLean.Foundations.Program.G32Native.EulerModel
