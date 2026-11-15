import HodgeLean.Foundations.Program.G32Native.StructureScalarTransport
import HodgeLean.Foundations.Program.G32Native.OriginalIdealOpenEquation

/-! # Original equation sections under source and ambient coordinate changes -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.Algebraic

/-- The structure-module inclusion of an ideal section is multiplication
by its actual value on one.
Source: `f5sheaf_scal_scalOf` and `f5sheaf_scalOf_eq`. -/
theorem idealSection_inclusion_eq_scalar {Q W : Scheme.{0}} (j : Q ⟶ W)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j)
    (c : Γ(W, ⊤))
    (hc : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app (.op ⊤)
      (s.val.app (.op ⊤) (1 : Γ(W, ⊤))) = c) :
    s ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) = f5sheaf_scal c := by
  let i := kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
  have h : f5sheaf_scalOf (s ≫ i) = c := hc
  exact (f5sheaf_scal_scalOf (s ≫ i)).symm.trans (congrArg f5sheaf_scal h)

/-- Source coordinate changes preserve the original scalar represented by
an ideal section.
Source: `original_ideal_source_iso_inclusion`. -/
theorem idealSection_source_transport_scalar {Q Q' W : Scheme.{0}}
    (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j)
    (c : Γ(W, ⊤))
    (hs : s ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) = f5sheaf_scal c) :
    (s ≫ (s2e_idealModule_source_iso j e).hom) ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (e.hom ≫ j).toRingCatSheafHom) =
        f5sheaf_scal c := by
  rw [Category.assoc, original_ideal_source_iso_inclusion, hs]

/-- Ambient coordinate changes carry the original scalar to the same
function in the inverse ambient coordinates.
Source: `original_ideal_target_iso_inclusion` and
`structureModule_scalar_conjugation`. -/
theorem idealSection_target_transport_scalar {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j)
    (c : Γ(W, ⊤))
    (hs : s ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) = f5sheaf_scal c) :
    (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward e.hom).map s ≫ (s2e_idealModule_target_pushforward_iso j e).hom) ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ≫ e.hom).toRingCatSheafHom) =
        f5sheaf_scal (e.inv.appTop c) := by
  letI := s2e_structureModule_map_isIso e.hom
  let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  let F := Scheme.Modules.pushforward e.hom
  let i := kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
  calc
    _ = η ≫ F.map s ≫ (s2e_idealModule_target_pushforward_iso j e).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ≫ e.hom).toRingCatSheafHom) := by
      simp only [η, F, Category.assoc]
    _ = η ≫ F.map s ≫ F.map i ≫ inv η := by rw [original_ideal_target_iso_inclusion]
    _ = η ≫ F.map (s ≫ i) ≫ inv η := by rw [Functor.map_comp, Category.assoc]
    _ = η ≫ F.map (f5sheaf_scal c) ≫ inv η := by rw [hs]
    _ = _ := structureModule_scalar_conjugation e c

/-- The intrinsic original ideal section represents its original regular
function as a structure-module endomorphism.
Source: `originalIdealOpenSection_inclusion_top` and
`idealSection_inclusion_eq_scalar`. -/
theorem originalIdealOpenSection_inclusion_scalar {Q W : Scheme.{0}} (j : Q ⟶ W)
    (A : W.Opens) (u : RingHom.ker (j.app A).hom) :
    originalIdealOpenSection j A u ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ∣_ A).toRingCatSheafHom) =
        f5sheaf_scal (A.topIso.inv u.val) :=
  idealSection_inclusion_eq_scalar (j ∣_ A) (originalIdealOpenSection j A u) _
    (originalIdealOpenSection_inclusion_top j A u)

#print axioms idealSection_inclusion_eq_scalar
#print axioms idealSection_source_transport_scalar
#print axioms idealSection_target_transport_scalar
#print axioms originalIdealOpenSection_inclusion_scalar
end HodgeLean.Foundations.TubularEuler
