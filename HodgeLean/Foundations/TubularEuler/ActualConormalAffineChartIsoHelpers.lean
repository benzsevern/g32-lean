import HodgeLean.Foundations.TubularEuler.ModuleAffinePointFibreHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalChartIsoHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers

/-! # The original affine open conormal chart isomorphism

The open restriction and original affine immersion comparison are shared by section and fibre constructions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

def actualConormalAffineChartIso
    {Q : Over (Spec (CommRingCat.of ℂ))} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) :
    (Scheme.Modules.pullback (hV.preimage j).isoSpec.inv).obj
      ((Scheme.Modules.pullback (j ⁻¹ᵁ V).ι).obj (Conormal.sheaf j)) ≅
      Conormal.sheaf (Spec.map (j.app V)) := by
  let U := j ⁻¹ᵁ V
  let eU : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅ Conormal.sheaf (j ∣_ V) :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (Conormal.sheaf j) ≪≫
      s2e_conormal_restrict_ambient_open_iso j V
  exact (Scheme.Modules.pullback (hV.preimage j).isoSpec.inv).mapIso eU ≪≫
    s2e_immersion_affine_chart_conormal_iso j V hV


#print axioms actualConormalAffineChartIso

end HodgeLean.Foundations.TubularEuler
