import HodgeLean.Foundations.Program.G32Native.ConormalAffinePointTransport
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealPointSection

/-! # Original local conormal classes in the actual ambient affine point fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The original local conormal class is the inverse image of the value
of its transported original affine ideal section. -/
theorem conormalAffinePointEquiv_localClass {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (d : ℕ) [SmoothOfRelativeDimension d W.hom] (x : ComplexPoint Q)
    (U : W.left.Opens) (hU : IsAffineOpen U) (hx : Point.map i x ∈ Point.overOpen U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    let ε : Γ(W.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom
      ((s2e_nativeAnalyticGerm_value d).comp
        (s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx))
    (conormalAffinePointEquiv i d x U hU hx).symm
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map (affineOpenIdealSection i.left U hU s))
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) = conormalLocalClass i U s x hx := by
  let ε : Γ(W.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom
    ((s2e_nativeAnalyticGerm_value d).comp
      (s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx))
  change (conormalPointFibreEquiv i x).symm
    ((affineOpenIdealPointEquiv i.left U hU (Point.map i x).left ε
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx)).symm _) = _
  rw [affineOpenIdealPointEquiv_section i.left U hU (Point.map i x) hx ε
    (affineOpenRegularGerm_point W d (Point.map i x) U hU hx) s]
  rfl

#print axioms conormalAffinePointEquiv_localClass
end HodgeLean.Foundations.Program.G32Native
