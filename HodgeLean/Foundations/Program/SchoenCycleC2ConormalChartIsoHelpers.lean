import HodgeLean.Foundations.Program.SchoenCycleC2ImmersionChartMapHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalIsoHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- In the canonical affine charts, the actual restricted conormal is the
conormal of the spectrum of the actual immersion section map. -/
def s2e_immersion_affine_chart_conormal_iso
    {Q W : Scheme.{0}} (ι : Q ⟶ W) [IsClosedImmersion ι]
    (V : W.Opens) (hV : IsAffineOpen V) :
    let hP := hV.preimage ι
    (Scheme.Modules.pullback hP.isoSpec.inv).obj (s2c_conormal (ι ∣_ V)) ≅
      s2c_conormal (Spec.map (ι.app V)) := by
  let hP := hV.preimage ι
  let g := hP.isoSpec.inv ≫ (ι ∣_ V)
  have hmap : g ≫ hV.isoSpec.hom = Spec.map (ι.app V) := by
    simpa only [g, Category.assoc] using s2e_closedImmersion_affine_chart_map ι V hV
  exact s2e_conormal_source_iso (ι ∣_ V) hP.isoSpec.symm ≪≫
    (s2e_conormal_target_iso g hV.isoSpec).symm ≪≫
    eqToIso (congrArg s2c_conormal hmap)

end HodgeLean.Foundations.Program
