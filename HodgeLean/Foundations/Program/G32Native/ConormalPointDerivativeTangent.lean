import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeMap
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSectionKernel
import HodgeLean.Foundations.Program.G32Native.ConormalLocalDifferential

/-! # The original immersion tangent image in the actual conormal pairing -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The original conormal point derivative annihilates the original
immersion tangent map, with the specified source and ambient charts. -/
theorem conormalPointDerivativeMap_tangent {Q W : Over (Spec ↧ℂ)}
    (n d : ℕ) [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension d W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left] (x : ComplexPoint Q)
    (U : W.left.Opens) (hU : IsAffineOpen U) (hx : Point.map i x ∈ Point.overOpen U) :
    (conormalPointDerivativeMap i d x U hU hx).comp
      (fderiv ℂ (inclusionInComplexCharts W Q i n d x) (localChart Q n x x)).toLinearMap = 0 := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let εR : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := εR.hom.toAlgebra
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let M := Conormal.idealModule j
  letI := s2e_idealModule_spec_fromTilde_isIso R j
  let q := liftToOpen Q (i.left ⁻¹ᵁ U) x (immersionPoint_mem_preimage i U x hx)
  have hq : q ≫ j = Spec.map εR :=
    affineOpenImmersionPoint_factorization i U hU x hx εR
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)
  have hz (m : (moduleSpecΓFunctor (R := R)).obj M) :
      s2e_nativeAnalyticGerm_value d (φ (affineIdealSectionInclusion R j m)) = 0 :=
    affineIdealSectionInclusion_map_zero R (CommRingCat.of ℂ) εR j q hq m
  let eD := affinePointDualEquiv R εR M
  let T := (conormalAffinePointEquiv i d x U hU hx).dualMap
  apply LinearMap.ext
  intro v
  apply T.symm.injective
  change T.symm (T (eD.symm (analyticModulePointDerivative d
    (fderiv ℂ (inclusionInComplexCharts W Q i n d x) (localChart Q n x x) v)
    φ (affineIdealSectionInclusion R j) hz))) = T.symm 0
  rw [T.symm_apply_apply, map_zero]
  apply eD.injective
  rw [eD.apply_symm_apply, map_zero]
  ext m
  change analyticPointDerivation d
    (fderiv ℂ (inclusionInComplexCharts W Q i n d x) (localChart Q n x x) v)
    φ (affineIdealSectionInclusion R j m) = 0
  rw [regularSection_pointDerivative]
  have hr : i.left.app U (affineIdealSectionInclusion R j m) = 0 :=
    (affineOpenIdealSectionKernelEquiv i.left U hU m).property
  exact regularEquation_derivative_tangent W Q i n d x U _ hx hr v

#print axioms conormalPointDerivativeMap_tangent
end HodgeLean.Foundations.Program.G32Native
