import HodgeLean.Foundations.Program.G32Native.ConormalPointFibreTransport
import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealPoint
import HodgeLean.Foundations.Program.G32Native.AffineOpenRegularGermPoint

/-! # Actual conormal point fibres on an ambient affine open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The original conormal fibre is the actual ideal fibre in canonical
affine coordinates, using the original regular germ's point map. -/
def conormalAffinePointEquiv {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (d : ℕ) [SmoothOfRelativeDimension d W.hom] (x : ComplexPoint Q)
    (U : W.left.Opens) (hU : IsAffineOpen U) (hx : Point.map i x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj (Conormal.sheaf i.left)) ≃ₗ[ℂ]
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        ((s2e_nativeAnalyticGerm_value d).comp
          (s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U hx))))).obj
        (Conormal.idealModule ((i.left ∣_ U) ≫ hU.isoSpec.hom))) :=
  (conormalPointFibreEquiv i x).trans
    (affineOpenIdealPointEquiv i.left U hU (Point.map i x).left _
      (affineOpenRegularGerm_point W d (Point.map i x) U hU hx))

#print axioms conormalAffinePointEquiv
end HodgeLean.Foundations.Program.G32Native
