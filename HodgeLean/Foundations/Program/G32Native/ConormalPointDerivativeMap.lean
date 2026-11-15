import HodgeLean.Foundations.Program.G32Native.ConormalAffinePointTransport
import HodgeLean.Foundations.Program.G32Native.AffineOpenImmersionPoint
import HodgeLean.Foundations.Program.G32Native.AnalyticModulePointMap
import HodgeLean.Foundations.Program.G32Native.AffineIdealSectionInclusion
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers

/-! # Original ambient derivatives on the actual source conormal fibre -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Original ambient tangent directions act on the actual source conormal
fibre through the original regular germs on an actual affine open. -/
def conormalPointDerivativeMap {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) :
    (Fin d → ℂ) →ₗ[ℂ] normalFibreOfModule (Conormal.sheaf i.left) x := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let q := liftToOpen Q (i.left ⁻¹ᵁ U) x (immersionPoint_mem_preimage i U x hx)
  have hq : q ≫ j = Spec.map ε :=
    affineOpenImmersionPoint_factorization i U hU x hx ε
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)
  letI : IsIso (Conormal.idealModule j).fromTildeΓ :=
    s2e_idealModule_spec_fromTilde_isIso R j
  have hz (m : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule j)) :
      s2e_nativeAnalyticGerm_value d (φ (affineIdealSectionInclusion R j m)) = 0 :=
    affineIdealSectionInclusion_map_zero R (CommRingCat.of ℂ) ε j q hq m
  exact (conormalAffinePointEquiv i d x U hU hx).dualMap.toLinearMap.comp
    (affineAnalyticModuleFunctionalMap d R φ (Conormal.idealModule j)
      (affineIdealSectionInclusion R j) hz)

/-- The original conormal derivative map retains the derivative of every
actual global ideal equation in its canonical ambient affine coordinates. -/
theorem conormalPointDerivativeMap_affineSection {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) (v : Fin d → ℂ)
    (s : unit (Spec Γ(W.left, U)) ⟶
      Conormal.idealModule ((i.left ∣_ U) ≫ hU.isoSpec.hom)) :
    let R := Γ(W.left, U)
    let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
    let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
    let γ := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback (Spec.map ε)).map s)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit (Spec.map ε)).inv
        (1 : Γ(Spec ↧ℂ, ⊤)))
    conormalPointDerivativeMap i d x U hU hx v
      ((conormalAffinePointEquiv i d x U hU hx).symm γ) =
      analyticPointDerivation d v φ
        (affineIdealSectionInclusion R ((i.left ∣_ U) ≫ hU.isoSpec.hom)
          (show (moduleSpecΓFunctor (R := R)).obj _ from
            s.val.app (Opposite.op ⊤) (1 : Γ(Spec R, ⊤)))) := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  letI : IsIso (Conormal.idealModule j).fromTildeΓ :=
    s2e_idealModule_spec_fromTilde_isIso R j
  let q := liftToOpen Q (i.left ⁻¹ᵁ U) x (immersionPoint_mem_preimage i U x hx)
  have hq : q ≫ j = Spec.map ε :=
    affineOpenImmersionPoint_factorization i U hU x hx ε
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)
  have hz (m : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule j)) :
      s2e_nativeAnalyticGerm_value d (φ (affineIdealSectionInclusion R j m)) = 0 :=
    affineIdealSectionInclusion_map_zero R (CommRingCat.of ℂ) ε j q hq m
  simp only [conormalPointDerivativeMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.dualMap_apply, LinearEquiv.apply_symm_apply,
    affineAnalyticModuleFunctionalMap_apply]
  exact affineAnalyticModuleFunctional_globalSection d v R φ (Conormal.idealModule j)
    (affineIdealSectionInclusion R j) hz s

#print axioms conormalPointDerivativeMap_affineSection
#print axioms conormalPointDerivativeMap
end HodgeLean.Foundations.Program.G32Native
