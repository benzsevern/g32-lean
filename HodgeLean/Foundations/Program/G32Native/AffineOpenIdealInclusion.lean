import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealTransport
import HodgeLean.Foundations.Program.G32Native.IdealOpenPullbackInclusion
import HodgeLean.Foundations.Program.G32Native.IdealTargetPullbackInclusion

/-! # Original ideal inclusions in the canonical ambient affine chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine-open ideal transport retains the original inclusion
and the original structure-module map of the canonical affine chart. -/
theorem affineOpenIdealPullback_inclusion {Q W : Scheme.{0}}
    (i : Q ⟶ W) (U : W.Opens) (hU : IsAffineOpen U) :
    (affineOpenIdealPullbackIso i U hU).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        ((i ∣_ U) ≫ hU.isoSpec.hom).toRingCatSheafHom) =
    (Scheme.Modules.pullback hU.fromSpec).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
      (pullbackUnit hU.fromSpec).hom := by
  let f := hU.isoSpec.inv
  let jI := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let E := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (Conormal.idealModule i) ≪≫
    s2e_idealModule_restrict_iso i U
  let C := Scheme.Modules.pullbackComp f U.ι
  have hn := C.inv.naturality jI
  change (Scheme.Modules.pullback hU.fromSpec).map jI ≫ (C.app (unit W)).inv =
    (C.app (Conormal.idealModule i)).inv ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback U.ι).map jI) at hn
  change (C.app (Conormal.idealModule i)).inv ≫
    (Scheme.Modules.pullback f).map E.hom ≫
      (idealTargetPullbackIso (i ∣_ U) hU.isoSpec).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          ((i ∣_ U) ≫ hU.isoSpec.hom).toRingCatSheafHom) = _
  rw [idealTargetPullback_inclusion, ← Functor.map_comp_assoc,
    idealOpenPullback_inclusion, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, pullbackUnit_composition_hom]
  change (Scheme.Modules.pullback hU.fromSpec).map jI ≫
    (C.app (unit W)).inv ≫ (C.app (unit W)).hom ≫ (pullbackUnit hU.fromSpec).hom =
      (Scheme.Modules.pullback hU.fromSpec).map jI ≫ (pullbackUnit hU.fromSpec).hom
  rw [Iso.inv_hom_id_assoc]

#print axioms affineOpenIdealPullback_inclusion
end HodgeLean.Foundations.Program.G32Native
