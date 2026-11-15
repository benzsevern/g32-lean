import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting the actual conormal to the inverse image of an ambient
scheme open gives the conormal of the same restricted morphism. -/
def s2e_conormal_restrict_ambient_open_iso
    {Q W : Scheme.{0}} (k : Q ⟶ W) (U : W.Opens) :
    Scheme.Modules.restrict (s2c_conormal k) (k ⁻¹ᵁ U).ι ≅
      s2c_conormal (k ∣_ U) :=
  (Scheme.Modules.restrictFunctorIsoPullback (k ⁻¹ᵁ U).ι).app (s2c_conormal k) ≪≫
    (Scheme.Modules.pullbackComp (k ⁻¹ᵁ U).ι k).app (s2c_idealModule k) ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι k U).symm).app (s2c_idealModule k) ≪≫
    (Scheme.Modules.pullbackComp (k ∣_ U) U.ι).symm.app (s2c_idealModule k) ≪≫
    (Scheme.Modules.pullback (k ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (s2c_idealModule k) ≪≫
        s2e_idealModule_restrict_iso k U)

end HodgeLean.Foundations.Program
