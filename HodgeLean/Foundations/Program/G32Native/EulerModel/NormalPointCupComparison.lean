import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointAbsoluteComparison
import HodgeLean.Foundations.Program.G32Native.EulerModel.ComponentCupComparison

/-! # Exact multiplicative comparison of the actual normalized coordinate point -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normalized coordinate-point coclass retains its exact canonical class under the multiplicative comparison. -/
theorem normalComponentPointCoclass_cupComparison
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    cupComparison Q (2 * k) (coordinate_class_at_degree Q k eQ
      (Finset.univ.erase 0) (by simp) k (by simp)) =
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (normalComponentPointCoclass k eQ) := by
  let (U : Opens (ComplexPoint Q)) : ParacompactSpace U := openParacompactSpace Q U
  apply (spec_singularToFieldCohomology_bijective ℚ Q (2 * k)).injective
  rw [bh11_cupComparison_eq_raw, singularToFieldCohomology_rationalCohomologyLinearEquivSingular]
  exact (normalComponentPointCoclass_absolute_comparison Q k eQ).symm

#print axioms normalComponentPointCoclass_cupComparison
/-- The actual kernel-section localization is exactly the signed multiplicative comparison of the canonical coordinate-point class. -/
theorem normalKernelSection_cupComparison_sign
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
          ((normalProjectivePointExcisionEquiv k (2 * k)).symm
            (relativeCohomologyMap ℚ (2 * k) (normalKernelLocalSectionPairMap k)
              (normalKernelLocalThomClass k)))) =
      (-1 : ℚ) ^ k • cupComparison Q (2 * k) (coordinate_class_at_degree Q k eQ
        (Finset.univ.erase 0) (by simp) k (by simp)) := by
  rw [normalKernelLocalThomClass_global_sign k, map_smul, map_smul]
  change (-1 : ℚ) ^ k • s2e_classToAbsolute Q _ k (normalComponentPointCoclass k eQ) = _
  rw [normalComponentPointCoclass_cupComparison Q k eQ]

#print axioms normalKernelSection_cupComparison_sign
end HodgeLean.Foundations.Program.G32Native.EulerModel
