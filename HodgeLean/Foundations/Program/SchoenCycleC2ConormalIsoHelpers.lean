import HodgeLean.Foundations.Program.SchoenCycleC2IdealTargetIsoHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pulling the actual conormal through a source isomorphism gives the
conormal of the same immersion in the new source coordinates. -/
def s2e_conormal_source_iso
    {Q Q' W : Scheme.{0}} (k : Q ⟶ W) (e : Q' ≅ Q) :
    (Scheme.Modules.pullback e.hom).obj (s2c_conormal k) ≅
      s2c_conormal (e.hom ≫ k) :=
  (Scheme.Modules.pullbackComp e.hom k).app (s2c_idealModule k) ≪≫
    (Scheme.Modules.pullback (e.hom ≫ k)).mapIso (s2e_idealModule_source_iso k e)

/-- An isomorphism of the ambient scheme retains the actual conormal
on the unchanged source scheme. -/
def s2e_conormal_target_iso
    {Q W W' : Scheme.{0}} (k : Q ⟶ W) (e : W ≅ W') :
    s2c_conormal (k ≫ e.hom) ≅ s2c_conormal k :=
  (Scheme.Modules.pullbackComp k e.hom).symm.app (s2c_idealModule (k ≫ e.hom)) ≪≫
    (Scheme.Modules.pullback k).mapIso
      ((Scheme.Modules.pullback e.hom).mapIso
          (s2e_idealModule_target_pushforward_iso k e).symm ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback e.hom).symm.app
          ((Scheme.Modules.pushforward e.hom).obj (s2c_idealModule k)) ≪≫
        (Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app (s2c_idealModule k))

end HodgeLean.Foundations.Program
