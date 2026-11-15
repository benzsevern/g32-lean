import HodgeLean.Foundations.Program.G32Native.IdealTargetPullback

/-! # The original ideal inclusion under an ambient isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual target-coordinate ideal isomorphism retains its original
inclusion into the structure module, with the specified unit comparison. -/
theorem idealTargetPushforward_inclusion {Q W W' : Scheme.{0}}
    (i : Q ⟶ W) (e : W ≅ W') :
    letI := s2e_structureModule_map_isIso e.hom
    (s2e_idealModule_target_pushforward_iso i e).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ≫ e.hom).toRingCatSheafHom) =
    (Scheme.Modules.pushforward e.hom).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
      inv (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) := by
  letI := s2e_structureModule_map_isIso e.hom
  simp only [s2e_idealModule_target_pushforward_iso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι, PreservesKernel.iso_hom,
    asIso_inv, Iso.symm_hom]
  rw [← Category.assoc, kernelComparison_comp_ι]

/-- Equality of the original defining morphisms retains their actual
kernel inclusions under the induced ideal-module transport. -/
theorem idealInclusion_congr {Q W : Scheme.{0}} {i j : Q ⟶ W} (h : i = j) :
    eqToHom (congrArg Conormal.idealModule h) ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
    kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) := by
  cases h
  exact Category.id_comp _

#print axioms idealInclusion_congr
#print axioms idealTargetPushforward_inclusion
end HodgeLean.Foundations.Program.G32Native
