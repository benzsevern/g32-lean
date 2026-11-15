import HodgeLean.Foundations.Program.G32Native.OriginalIdealOpenSections
import HodgeLean.Foundations.Algebraic.GrassmannianSheafGlue

/-! # Values of original module sections on smaller open subsets -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution HodgeLean.Foundations.Algebraic

/-- The open-section arrow represents the restriction of its original value on every open. -/
theorem moduleOpenSectionOfValue_app_one {W : Scheme.{0}} (M : W.Modules)
    (A : W.Opens) (t : Γ(M, A)) (O : A.toScheme.Opens) :
    (moduleOpenSectionOfValue M A t).val.app (op O) (1 : Γ(A.toScheme, O)) =
      M.presheaf.map (homOfLE (A.ι_image_le O)).op t := by
  let s := moduleOpenSectionOfValue M A t
  have h := congrArg (fun f => f (1 : Γ(A.toScheme, ⊤)))
    (s.val.naturality (homOfLE (le_top : O ≤ ⊤)).op)
  change s.val.app (op O) (A.toScheme.presheaf.map (homOfLE le_top).op 1) =
    ((Scheme.Modules.restrictFunctor A.ι).obj M).presheaf.map
      (homOfLE (le_top : O ≤ ⊤)).op (s.val.app (op ⊤) (1 : Γ(A.toScheme, ⊤))) at h
  rw [map_one] at h
  dsimp only [s] at h
  rw [moduleOpenSectionOfValue_top] at h
  exact h.trans (f5sheaf_map_map M (eqToHom A.ι_image_top)
    (A.ι.opensFunctor.map (homOfLE (le_top : O ≤ ⊤)))
    (homOfLE (A.ι_image_le O)) t)

/-- The original open-section arrow restricts to the arrow of the restricted value. -/
theorem moduleOpenSectionOfValue_restrict {W : Scheme.{0}} (M : W.Modules)
    {A B : W.Opens} (h : B ≤ A) (t : Γ(M, A)) :
    moduleOpenSectionOfValue M B (M.presheaf.map (homOfLE h).op t) ≫
        (f5sheaf_restrictNest h).hom.app M =
      (Scheme.Modules.restrictUnitIso (W.homOfLE h)).inv ≫
        (Scheme.Modules.restrictFunctor (W.homOfLE h)).map
          (moduleOpenSectionOfValue M A t) := by
  let b := W.homOfLE h
  apply (i1_module_unitHomEquivTop
    ((Scheme.Modules.restrictFunctor b).obj ((Scheme.Modules.restrictFunctor A.ι).obj M))).injective
  change ((f5sheaf_restrictNest h).hom.app M).val.app (op ⊤)
      ((moduleOpenSectionOfValue M B (M.presheaf.map (homOfLE h).op t)).val.app
        (op ⊤) (1 : Γ(B.toScheme, ⊤))) =
    (moduleOpenSectionOfValue M A t).val.app (op (b ''ᵁ ⊤))
      ((b.appIso ⊤).inv (1 : Γ(B.toScheme, ⊤)))
  have h1 : (b.appIso ⊤).inv (1 : Γ(B.toScheme, ⊤)) =
      (1 : Γ(A.toScheme, b ''ᵁ ⊤)) := map_one _
  rw [h1, moduleOpenSectionOfValue_app_one M A t (b ''ᵁ ⊤),
    moduleOpenSectionOfValue_top M B (M.presheaf.map (homOfLE h).op t)]
  erw [f5sheaf_restrictNest_app h M ⊤]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ t)) =
    M.presheaf.map _ t
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end HodgeLean.Foundations.TubularEuler
