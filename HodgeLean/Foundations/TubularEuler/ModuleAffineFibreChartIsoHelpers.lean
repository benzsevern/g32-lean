import HodgeLean.Foundations.TubularEuler.ModuleAffineFibreChartMapHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoCompositeValueHelpers

/-! # Isomorphisms for the original affine chart fibre transport

The open fibre map, specified affine chart and original point presentation are retained.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

def moduleAffineFibreChartIso
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_moduleFibre M x ≅ (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))).obj N) :=
  moduleAffinePointFibreIso M U hU x hx ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).mapIso e) ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
      ((Scheme.Modules.pullbackCongr
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).app N)

theorem moduleAffineFibreChartIso_eq
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    moduleAffineFibreChartIso M U hU N e x hx =
      moduleAffinePointFibreIso M U hU x hx ≪≫
        (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
          ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).mapIso e) ≪≫
        (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
          ((Scheme.Modules.pullbackCongr
            (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).app N) := by
  rfl

#print axioms moduleAffineFibreChartIso_eq

#print axioms moduleAffineFibreChartIso

end HodgeLean.Foundations.TubularEuler
