import HodgeLean.Foundations.TubularEuler.ModuleAffineFibreChartIsoHelpers

/-! # Evaluation of the original affine chart fibre isomorphism

The specified open fibre and affine point maps are evaluated before section specialization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem moduleAffineFibreChartIso_apply_eq
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (w : i1_moduleFibre M x)
    (y : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))).obj N))
    (h : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (((Scheme.Modules.pullbackCongr
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).app N).hom)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).mapIso e).hom)
        ((moduleAffinePointFibreIso M U hU x hx).hom w)) = y) :
    (moduleAffineFibreChartIso M U hU N e x hx).hom w = y := by
  exact moduleIso_apply_eq_of_two_maps (moduleSpecΓFunctor (R := CommRingCat.of ℂ))
    (moduleAffinePointFibreIso M U hU x hx)
    ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).mapIso e)
    ((Scheme.Modules.pullbackCongr
      (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).app N)
    (moduleAffineFibreChartIso M U hU N e x hx)
    (moduleAffineFibreChartIso_eq M U hU N e x hx) w y h

theorem moduleAffineFibreChartIso_apply_eq_raw
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (w : i1_moduleFibre M x)
    (y : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))).obj N))
    (h : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).map e.hom)
        ((moduleAffinePointFibreIso M U hU x hx).hom w)) = y) :
    (moduleAffineFibreChartIso M U hU N e x hx).hom w = y := by
  exact moduleIso_apply_eq_of_functor_natIso (moduleSpecΓFunctor (R := CommRingCat.of ℂ))
    (Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))
    (Scheme.Modules.pullback (Spec.map (Spec.preimage
      (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))))
    (Scheme.Modules.pullbackCongr
      (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm)
    (moduleAffinePointFibreIso M U hU x hx) e
    (moduleAffineFibreChartIso M U hU N e x hx)
    (moduleAffineFibreChartIso_eq M U hU N e x hx) w y h

#print axioms moduleAffineFibreChartIso_apply_eq_raw

#print axioms moduleAffineFibreChartIso_apply_eq

end HodgeLean.Foundations.TubularEuler
