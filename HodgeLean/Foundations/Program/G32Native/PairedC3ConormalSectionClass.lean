import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeMap
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealPointSection
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealEquation

/-! # Original local equations in the actual conormal point derivative -/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The original affine section represents the actual local conormal class. -/
theorem conormalPointDerivativeMap_section_class {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let t := affineOpenIdealSection i.left U hU s
  let γ := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullback (Spec.map ε)).map t)
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
      (1 : Γ(Spec ↧ℂ, ⊤)))
  (conormalAffinePointEquiv i d x U hU hx).symm γ = conormalLocalClass i U s x hx := by
  let R := Γ(W.left, U)
  let φ := s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let t := affineOpenIdealSection i.left U hU s
  let γ := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullback (Spec.map ε)).map t)
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
      (1 : Γ(Spec ↧ℂ, ⊤)))
  change (conormalPointFibreEquiv i x).symm
    ((affineOpenIdealPointEquiv i.left U hU (Point.map i x).left ε
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)).symm γ) = _
  exact congrArg (conormalPointFibreEquiv i x).symm
    (affineOpenIdealPointEquiv_section i.left U hU (Point.map i x) hx ε
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx) s)

#print axioms conormalPointDerivativeMap_section_class
end HodgeLean.Foundations.Program.G32Native
