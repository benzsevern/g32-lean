import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalHyperplaneNormalization

/-! # Exact signed hyperplane top power on the supplied actual projective component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual kernel-section localization is the exact signed top power of the same supplied normalized hyperplane coclass on the specified component. -/
theorem normalKernelSection_hyperplane_sign
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
          ((normalProjectivePointExcisionEquiv k (2 * k)).symm
            (relativeCohomologyMap ℚ (2 * k) (normalKernelLocalSectionPairMap k)
              (normalKernelLocalThomClass k)))) =
      (-1 : ℚ) ^ k • s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
        (s2e_classToAbsolute Q
          (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k := by
  rw [normalKernelLocalThomClass_global_sign k, map_smul, map_smul]
  change (-1 : ℚ) ^ k • s2e_classToAbsolute Q _ k (normalComponentPointCoclass k eQ) = _
  rw [normalComponentPointCoclass_hyperplane_power Q k hk eQ cH hcH]

#print axioms normalKernelSection_hyperplane_sign
end HodgeLean.Foundations.Program.G32Native.EulerModel
