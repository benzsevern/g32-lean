import HodgeLean.Foundations.TubularEuler.ActualConormalSectionChartHelpers
import HodgeLean.Foundations.TubularEuler.ModuleAffineSectionDataHelpers

/-! # Descended section data for the original affine immersion ideal

The section is selected through the actual open restriction and affine conormal isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

opaque actualConormalAffineSectionData
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (u : RingHom.ker (j.app V).hom) :
    ModuleAffineSectionData (Conormal.sheaf j) (j ⁻¹ᵁ V) (hV.preimage j)
      (Conormal.sheaf (Spec.map (j.app V))) (actualConormalAffineChartIso j V hV)
      (affineConormalSection (W.presheaf.obj (.op V))
        (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u) :=
  moduleAffineSectionDataOfIso (Conormal.sheaf j) (j ⁻¹ᵁ V) (hV.preimage j)
    (Conormal.sheaf (Spec.map (j.app V))) (actualConormalAffineChartIso j V hV)
    (affineConormalSection (W.presheaf.obj (.op V))
      (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u)

theorem actualConormalAffineSectionData_point_value
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (u : RingHom.ker (j.app V).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    let M : Q.left.Modules := Conormal.sheaf j
    let U : Q.left.Opens := j ⁻¹ᵁ V
    let hU : IsAffineOpen U := hV.preimage j
    let N : (Spec (Q.left.presheaf.obj (.op U))).Modules := Conormal.sheaf (Spec.map (j.app V))
    let e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N :=
      actualConormalAffineChartIso j V hV
    let t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N :=
      affineConormalSection (W.presheaf.obj (.op V))
        (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u
    let d : ModuleAffineSectionData M U hU N e t := actualConormalAffineSectionData j V hV u
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).map e.hom)
        ((moduleAffinePointFibreIso M U hU x hx).hom
          (i1_moduleSectionValue M U d.localSection x hx))) =
      i1_module_pointValue N t
        (Spec.map (Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))) := by
  intro M U hU N e t d
  exact @ModuleAffineSectionData.point_value Q M U hU N e t d x hx

theorem actualConormalAffineSectionData_point_value_iso
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (u : RingHom.ker (j.app V).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    let M : Q.left.Modules := Conormal.sheaf j
    let U : Q.left.Opens := j ⁻¹ᵁ V
    let hU : IsAffineOpen U := hV.preimage j
    let N : (Spec (Q.left.presheaf.obj (.op U))).Modules := Conormal.sheaf (Spec.map (j.app V))
    let e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N :=
      actualConormalAffineChartIso j V hV
    let t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N :=
      affineConormalSection (W.presheaf.obj (.op V))
        (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u
    let d : ModuleAffineSectionData M U hU N e t := actualConormalAffineSectionData j V hV u
    (moduleAffineFibreChartIso M U hU N e x hx).hom
      (i1_moduleSectionValue M U d.localSection x hx) =
      i1_module_pointValue N t (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))) := by
  intro M U hU N e t d
  exact @ModuleAffineSectionData.point_value_iso Q M U hU N e t d x hx

#print axioms actualConormalAffineSectionData_point_value_iso

#print axioms actualConormalAffineSectionData_point_value

#print axioms actualConormalAffineSectionData

end HodgeLean.Foundations.TubularEuler
