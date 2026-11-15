import HodgeLean.Foundations.TubularEuler.ModuleAffinePointPresentationHelpers

/-! # The canonical affine chart map on actual module fibres

The map is the composite of the original open fibre comparison, supplied affine module map and point presentation comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

def moduleAffineFibreChartMap
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (f : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ⟶ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_moduleFibre M x ⟶ (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))).obj N) :=
  (moduleAffinePointFibreIso M U hU x hx).hom ≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).map f) ≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).hom.app N)

#print axioms moduleAffineFibreChartMap

end HodgeLean.Foundations.TubularEuler
