import HodgeLean.Foundations.TubularEuler.ActualConormalFibreAffineHelpers
import HodgeLean.Foundations.TubularEuler.ActualConormalAffineChartIsoHelpers
import HodgeLean.Foundations.TubularEuler.ModuleSectionIsoDescentHelpers
import HodgeLean.Foundations.TubularEuler.AffineConormalSectionFibreHelpers

/-! # Original conormal sections on the specified affine open chart

The actual open restriction and affine immersion comparison transport the original ideal section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution


theorem actualConormalAffineChartSection_exists
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (u : RingHom.ker (j.app V).hom) :
    ∃ s : SheafOfModules.unit.{0} (j ⁻¹ᵁ V).toScheme.ringCatSheaf ⟶
        (Scheme.Modules.pullback (j ⁻¹ᵁ V).ι).obj (Conormal.sheaf j),
      i1_module_sectionPullback (hV.preimage j).isoSpec.inv
          ((Scheme.Modules.pullback (j ⁻¹ᵁ V).ι).obj (Conormal.sheaf j)) s ≫
        (actualConormalAffineChartIso j V hV).hom =
          affineConormalSection (W.presheaf.obj (.op V))
            (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u := by
  exact moduleSection_iso_transport_exists (hV.preimage j).isoSpec.symm
    ((Scheme.Modules.pullback (j ⁻¹ᵁ V).ι).obj (Conormal.sheaf j))
    (Conormal.sheaf (Spec.map (j.app V))) (actualConormalAffineChartIso j V hV)
    (affineConormalSection (W.presheaf.obj (.op V))
      (Q.left.presheaf.obj (.op (j ⁻¹ᵁ V))) (j.app V) u)

#print axioms actualConormalAffineChartSection_exists

#print axioms actualConormalAffineChartIso

end HodgeLean.Foundations.TubularEuler
