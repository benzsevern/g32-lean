import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A frame on an isomorphic neighbourhood chart gives a frame for the
actual restriction to the same scheme open. -/
def s2e_restrict_frame_of_iso_factor
    {X U V : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : V ⟶ X) (e : U ≅ V) (h : e.hom ≫ i = j)
    (M : X.Modules) (k : ℕ)
    (b : (Scheme.Modules.pullback i).obj M ≅
      (SheafOfModules.free (R := V.ringCatSheaf) (Fin k) : V.Modules)) :
    Scheme.Modules.restrict M j ≅
      (SheafOfModules.free (R := U.ringCatSheaf) (Fin k) : U.Modules) := by
  let : (SheafOfModules.pushforward.{0} e.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward e.hom).IsRightAdjoint
  exact (Scheme.Modules.restrictFunctorIsoPullback j).app M ≪≫
    (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
    (Scheme.Modules.pullbackComp e.hom i).symm.app M ≪≫
    (Scheme.Modules.pullback e.hom).mapIso b ≪≫
    SheafOfModules.pullbackObjFreeIso e.hom.toRingCatSheafHom (Fin k)

/-- A frame pulled back to an actual open-immersion chart gives a frame
on its actual image neighbourhood. -/
theorem s2e_openImmersion_frame_neighbourhood
    {X T : Scheme.{0}} (j : T ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (k : ℕ)
    (b : (Scheme.Modules.pullback j).obj M ≅
      (SheafOfModules.free (R := T.ringCatSheaf) (Fin k) : T.Modules))
    (x : X) (hx : x ∈ Set.range j) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (Scheme.Modules.restrict M U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  refine ⟨j.opensRange, hx, ⟨?_⟩⟩
  exact s2e_restrict_frame_of_iso_factor j.opensRange.ι j j.isoOpensRange.symm
    j.isoOpensRange_inv_comp M k b

end HodgeLean.Foundations.Program
