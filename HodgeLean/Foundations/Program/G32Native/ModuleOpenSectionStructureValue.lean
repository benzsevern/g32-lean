import HodgeLean.Foundations.Program.G32Native.OriginalIdealOpenSections

/-! # Structure-module values of original sections on an open subscheme -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- An original open module section followed by a structure-module arrow
has the same regular function value on the open subscheme.
Source: naturality of the module arrow and `moduleOpenSectionOfValue_top`. -/
theorem moduleOpenSectionOfValue_structure_top
    {W : Scheme.{0}} (M : W.Modules) (A : W.Opens) (t : Γ(M, A))
    (i : M ⟶ SheafOfModules.unit W.ringCatSheaf) :
    (moduleOpenSectionOfValue M A t ≫ (Scheme.Modules.restrictFunctor A.ι).map i ≫
      (Scheme.Modules.restrictUnitIso A.ι).hom).val.app (.op ⊤) (1 : Γ(A.toScheme, ⊤)) =
      A.topIso.inv (i.val.app (.op A) t) := by
  change (A.ι.appIso ⊤).hom
    (i.val.app (.op (A.ι ''ᵁ ⊤))
      ((moduleOpenSectionOfValue M A t).val.app (.op ⊤) (1 : Γ(A.toScheme, ⊤)))) = _
  rw [moduleOpenSectionOfValue_top]
  have h := congrArg (fun f => f t) (i.val.naturality (eqToHom A.ι_image_top).op)
  change i.val.app (.op (A.ι ''ᵁ ⊤)) (M.val.map (eqToHom A.ι_image_top).op t) =
    W.presheaf.map (eqToHom A.ι_image_top).op (i.val.app (.op A) t) at h
  rw [h, A.ι_appIso]
  rfl

#print axioms moduleOpenSectionOfValue_structure_top
end HodgeLean.Foundations.TubularEuler
