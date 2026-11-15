import HodgeLean.Foundations.Program.G32Native.ModuleOpenSectionStructureValue

/-! # Intrinsic ideal sections of original regular equations on ambient opens -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

/-- The original ideal equation as a section of the actual restricted
immersion ideal, before taking its conormal pullback.
Source: `s2e_idealModule_sections_equiv` and `s2e_idealModule_restrict_iso`;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
def originalIdealOpenSection {Q W : Scheme.{0}} (j : Q ⟶ W)
    (A : W.Opens) (u : RingHom.ker (j.app A).hom) :
    SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶ Conormal.idealModule (j ∣_ A) :=
  moduleOpenSectionOfValue (Conormal.idealModule j) A
      ((s2e_idealModule_sections_equiv j A).symm u) ≫
    (s2e_idealModule_restrict_iso j A).hom

/-- The intrinsic restricted ideal section includes into the structure
module as the same original regular equation on the open subscheme.
Source: `original_ideal_restriction_inclusion` and
`moduleOpenSectionOfValue_structure_top`. -/
theorem originalIdealOpenSection_inclusion_top {Q W : Scheme.{0}} (j : Q ⟶ W)
    (A : W.Opens) (u : RingHom.ker (j.app A).hom) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ∣_ A).toRingCatSheafHom)).val.app (.op ⊤)
      ((originalIdealOpenSection j A u).val.app (.op ⊤) (1 : Γ(A.toScheme, ⊤))) =
      A.topIso.inv u.val := by
  let I := Conormal.idealModule j
  let t := (s2e_idealModule_sections_equiv j A).symm u
  let s := moduleOpenSectionOfValue I A t
  let i := kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
  have h := congrArg (fun f : SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit.{0} A.toScheme.ringCatSheaf =>
      f.val.app (.op ⊤) (1 : Γ(A.toScheme, ⊤)))
    (congrArg (fun f => s ≫ f) (original_ideal_restriction_inclusion j A))
  have ht : i.val.app (.op A) t = u.val :=
    (s2e_idealModule_sections_equiv_coe j A t).symm.trans
      (congrArg Subtype.val ((s2e_idealModule_sections_equiv j A).apply_symm_apply u))
  exact h.trans ((moduleOpenSectionOfValue_structure_top I A t i).trans
    (congrArg A.topIso.inv ht))

#print axioms originalIdealOpenSection_inclusion_top
end HodgeLean.Foundations.TubularEuler
