import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeMap
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSectionKernel
import HodgeLean.Foundations.Program.G32Native.AffineOpenSmoothAlgebra
import HodgeLean.Foundations.Program.G32Native.RegularSectionValueAlgebra
import HodgeLean.Foundations.Program.G32Native.OverSpecSectionMap
import HodgeLean.Foundations.Program.G32Native.EtaleAnalyticIdealExtension

/-! # Surjectivity on the original source conormal point fibre -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- In specified original etale coordinates, original ambient tangent
directions fill the actual source dual conormal fibre of a smooth immersion. -/
theorem conormalPointDerivativeMap_surjective {Q W : Over (Spec ↧ℂ)}
    (n d : ℕ) [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension d W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left] (x : ComplexPoint Q)
    (U : W.left.Opens) (hU : IsAffineOpen U) (hx : Point.map i x ∈ Point.overOpen U) :
    letI := overSpecAlgebra W U
    ∀ (c : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(W.left, U)) (hc : c.toRingHom.Etale)
      (a : Fin d → ℂ)
      (hcoord : ∀ t, s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
        (c (MvPolynomial.X t)) = s2e_nativeAnalytic_constant d (a t) +
          s2e_nativeAnalytic_coordinate d t),
      Function.Surjective (conormalPointDerivativeMap i d x U hU hx) := by
  letI : Smooth W.hom := SmoothOfRelativeDimension.smooth d W.hom
  letI : Smooth Q.hom := SmoothOfRelativeDimension.smooth n Q.hom
  let R := Γ(W.left, U)
  let V := i.left ⁻¹ᵁ U
  let B := Γ(Q.left, V)
  letI := overSpecAlgebra W U
  letI := overSpecAlgebra Q V
  change ∀ (c : MvPolynomial (Fin d) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (a : Fin d → ℂ)
    (hcoord : ∀ t, s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
      (c (MvPolynomial.X t)) = s2e_nativeAnalytic_constant d (a t) +
        s2e_nativeAnalytic_coordinate d t),
    Function.Surjective (conormalPointDerivativeMap i d x U hU hx)
  intro c hc a hcoord
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let εR : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := εR.hom.toAlgebra
  let χ : R →ₐ[ℂ] B := overSpecSectionMap i U
  let P := Algebra.Extension.ofSurjective χ (i.left.app_surjective U hU)
  letI : Algebra.FormallySmooth ℂ R := by
    letI := affineOpen_smoothAlgebra W U hU
    infer_instance
  letI : Algebra.FormallySmooth ℂ B := by
    letI := affineOpen_smoothAlgebra Q V (hU.preimage i.left)
    infer_instance
  letI : Algebra.FormallySmooth ℂ P.Ring := by
    change Algebra.FormallySmooth ℂ R
    infer_instance
  let εB : B →ₐ[ℂ] ℂ := regularSectionValueAlgHom Q n x V
    (immersionPoint_mem_preimage i U x hx)
  have hε (r : R) : εB (algebraMap P.Ring B r) = s2e_nativeAnalyticGerm_value d (φ r) := by
    change regularSectionValueAlgHom Q n x V _ (i.left.app U r) =
      s2e_nativeAnalyticGerm_value d (φ r)
    rw [regularSectionValueAlgHom_apply, s2e_regularSection_nativeAnalyticGerm_value]
    exact (Point.evaluate_map i U r x).symm
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let M := Conormal.idealModule j
  letI := s2e_idealModule_spec_fromTilde_isIso R j
  let q := liftToOpen Q V x (immersionPoint_mem_preimage i U x hx)
  have hq : q ≫ j = Spec.map εR :=
    affineOpenImmersionPoint_factorization i U hU x hx εR
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)
  have hz (m : (moduleSpecΓFunctor (R := R)).obj M) :
      s2e_nativeAnalyticGerm_value d (φ (affineIdealSectionInclusion R j m)) = 0 :=
    affineIdealSectionInclusion_map_zero R (CommRingCat.of ℂ) εR j q hq m
  let eI : (moduleSpecΓFunctor (R := R)).obj M ≃ₗ[R] P.ker :=
    affineOpenIdealSectionKernelEquiv i.left U hU
  let eD := affinePointDualEquiv R εR M
  let T := (conormalAffinePointEquiv i d x U hU hx).dualMap
  intro ν
  let f : P.ker →ₗ[R] ℂ := (eD (T.symm ν)).comp eI.symm.toLinearMap
  obtain ⟨v, hv⟩ := etaleAnalyticIdealFunctional_extends d P φ
    (regularGermMap_complexConstants W d (Point.map i x) U hx) c hc a hcoord εB hε f
  refine ⟨v, ?_⟩
  apply T.symm.injective
  change T.symm (T (eD.symm (analyticModulePointDerivative d v φ
    (affineIdealSectionInclusion R j) hz))) = T.symm ν
  rw [T.symm_apply_apply]
  apply eD.injective
  rw [eD.apply_symm_apply]
  ext m
  have hm := hv (eI m)
  change analyticPointDerivation d v φ (affineIdealSectionInclusion R j m) =
    (eD (T.symm ν)) (eI.symm (eI m)) at hm
  rw [eI.symm_apply_apply] at hm
  exact hm

#print axioms conormalPointDerivativeMap_surjective
end HodgeLean.Foundations.Program.G32Native
