import HodgeLean.Foundations.TubularEuler.ModuleAffineSectionTransportHelpers
import HodgeLean.Foundations.TubularEuler.ModulePointPresentationHelpers
import HodgeLean.Foundations.TubularEuler.ModuleSectionIsoDescentHelpers

/-! # Actual affine section values in the selected point presentation

The original affine point is retained before the Spec presentation comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem moduleAffinePointFibreIso_section_pointPresentation
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (f : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ⟶ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr (Spec.map_preimage b).symm).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback b).map f)
        ((moduleAffinePointFibreIso M U hU x hx).hom (i1_moduleSectionValue M U s x hx))) =
      i1_module_pointValue N
        (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s ≫ f)
        (Spec.map (Spec.preimage b)) := by
  have h := congrArg (fun t => (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).map f) t))
    (moduleAffinePointFibreIso_section_value M U hU s x hx)
  exact h.trans (modulePointValue_naturality_presentation
    ((Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M)) N f
    (i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) s)
    (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom) (Spec.map (Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))) (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm)

theorem moduleAffineSection_transport_point_values_exists
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N) :
    ∃ s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M,
      ∀ (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U),
        let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
        (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          ((Scheme.Modules.pullbackCongr (Spec.map_preimage b).symm).hom.app N)
          ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback b).map e.hom)
            ((moduleAffinePointFibreIso M U hU x hx).hom (i1_moduleSectionValue M U s x hx))) =
          i1_module_pointValue N t (Spec.map (Spec.preimage b)) := by
  obtain ⟨s, hs⟩ := moduleSection_iso_transport_exists hU.isoSpec.symm
    ((Scheme.Modules.pullback U.ι).obj M) N e t
  refine ⟨s, ?_⟩
  intro x hx
  have h := moduleAffinePointFibreIso_section_pointPresentation M U hU s N e.hom x hx
  have ht := congrArg (fun z : SheafOfModules.unit.{0}
      (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N =>
    i1_module_pointValue N z
      (Spec.map (Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))) hs
  exact h.trans ht

#print axioms moduleAffineSection_transport_point_values_exists

#print axioms moduleAffinePointFibreIso_section_pointPresentation


end HodgeLean.Foundations.TubularEuler
