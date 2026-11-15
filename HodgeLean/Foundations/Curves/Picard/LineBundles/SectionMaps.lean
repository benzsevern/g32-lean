import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Module morphisms from sections on an open

The construction uses the actual restriction functor and its coefficient maps.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- A section on an open defines a morphism from its structure module. -/
def localSectionHom {X : Scheme} (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    unit U.toScheme ⟶ M.restrict U.ι :=
  (M.restrict U.ι).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun V =>
      M.val.map (homOfLE (U.ι_image_le V.unop)).op s) (by
        intro V W f
        change M.val.map (U.ι.opensFunctor.map f.unop).op
          (M.val.map (homOfLE (U.ι_image_le V.unop)).op s) =
            M.val.map (homOfLE (U.ι_image_le W.unop)).op s
        rw [← PresheafOfModules.map_comp_apply]
        rfl))

theorem localSectionHom_app {X : Scheme} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (V : U.toScheme.Opens) (r : Γ(U.toScheme, V)) :
    (localSectionHom M U s).val.app (Opposite.op V) r =
      (U.ι.appIso V).inv r • M.presheaf.map (homOfLE (U.ι_image_le V)).op s := by
  rfl

/-- An isomorphism test for module sheaves on the affine open basis. -/
theorem module_isIso_of_affine_app {X : Scheme} {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ U : X.affineOpens, Function.Bijective (f.app U.1)) : IsIso f := by
  haveI : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : X.affineOpens => U.1)
      (by simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using X.isBasis_affineOpens)
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hf U)
  haveI : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)))
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

end HodgeLean.Foundations.Curves.Picard.LineBundles
