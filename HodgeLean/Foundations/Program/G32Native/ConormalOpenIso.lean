import HodgeLean.Foundations.Program.G32Native.SubschemeOpenIso
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalIsoHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers

/-! Transport the actual conormal to the subscheme of a restricted ideal. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual conormal of an ideal restricted to an open is the pulled original conormal. -/
def g32l4_conormal_comap_open_iso {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) :
    (Scheme.Modules.pullback ((g32l4_subscheme_comap_open_iso I U).hom ≫
      (I.subschemeι ⁻¹ᵁ U).ι)).obj (s2c_conormal I.subschemeι) ≅
        s2c_conormal (I.comap U.ι).subschemeι := by
  let e := g32l4_subscheme_comap_open_iso I U
  let P := I.subschemeι ⁻¹ᵁ U
  let : (SheafOfModules.pushforward e.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward e.hom).IsRightAdjoint
  exact (Scheme.Modules.pullbackComp e.hom P.ι).symm.app (s2c_conormal I.subschemeι) ≪≫
    (Scheme.Modules.pullback e.hom).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback P.ι).symm.app
        (s2c_conormal I.subschemeι) ≪≫
        s2e_conormal_restrict_ambient_open_iso I.subschemeι U) ≪≫
    s2e_conormal_source_iso (I.subschemeι ∣_ U) e ≪≫
    eqToIso (congrArg (fun k => s2c_conormal k)
      (g32l4_subscheme_comap_open_iso_hom_restrict I U))

end HodgeLean.Foundations.Program
