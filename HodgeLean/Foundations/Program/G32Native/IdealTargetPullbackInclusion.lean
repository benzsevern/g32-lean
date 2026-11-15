import HodgeLean.Foundations.Program.G32Native.IdealTargetInclusion
import HodgeLean.Foundations.Program.G32Native.OpenAdjointInclusionTransport

/-! # The original ideal inclusion under inverse ambient pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual inverse ambient ideal transport retains the original
inclusion with its original pullback structure-module comparison. -/
theorem idealTargetPullback_inclusion {Q W W' : Scheme.{0}}
    (i : Q ⟶ W) (e : W ≅ W') :
    (idealTargetPullbackIso i e).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ≫ e.hom).toRingCatSheafHom) =
    (Scheme.Modules.pullback e.inv).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
      (pullbackUnit e.inv).hom := by
  let j := i ≫ e.hom
  have hj : j ≫ e.inv = i := by simp [j]
  let E : (Scheme.Modules.pushforward e.inv).obj (Conormal.idealModule j) ≅
      Conormal.idealModule i :=
    s2e_idealModule_target_pushforward_iso j e.symm ≪≫
      eqToIso (congrArg Conormal.idealModule hj)
  letI := s2e_structureModule_map_isIso e.inv
  let η := SheafOfModules.unitToPushforwardObjUnit e.inv.toRingCatSheafHom
  let jI := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let jJ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
  have he : E.hom ≫ jI = (Scheme.Modules.pushforward e.inv).map jJ ≫ inv η := by
    change (s2e_idealModule_target_pushforward_iso j e.symm).hom ≫
      eqToHom (congrArg Conormal.idealModule hj) ≫ jI = _
    rw [idealInclusion_congr hj]
    exact idealTargetPushforward_inclusion j e.symm
  have ha : E.inv ≫ (Scheme.Modules.pushforward e.inv).map jJ = jI ≫ pushforwardUnit e.inv := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, he, Category.assoc]
    change _ = (Scheme.Modules.pushforward e.inv).map jJ ≫ inv η ≫ η
    rw [IsIso.inv_hom_id, Category.comp_id]
  exact openAdjointTransport_inclusion e.inv (Conormal.idealModule i)
    (Conormal.idealModule j) E jI jJ ha

#print axioms idealTargetPullback_inclusion
end HodgeLean.Foundations.Program.G32Native
