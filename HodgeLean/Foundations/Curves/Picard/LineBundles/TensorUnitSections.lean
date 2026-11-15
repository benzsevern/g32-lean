import HodgeLean.Foundations.Curves.Picard.LineBundles.TensorSections

/-! # Tensor unit comparisons on actual sections

The sheafification adjunction identifies the unit comparison with scalar action.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The tensor unit comparison is adjoint to the sectionwise scalar action. -/
theorem tensorUnit_adjunct {X : Scheme} (M : X.Modules) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) (tensorUnit M).hom =
      (MonoidalCategory.leftUnitor
        (show PresheafOfModulesOfCommRing X.presheaf from M.val)).hom := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change A.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (MonoidalCategory.leftUnitor
        (show PresheafOfModulesOfCommRing X.presheaf from M.val)).hom ≫ A.counit.app M) = _
  rw [Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_symm_id]
  erw [Equiv.apply_symm_apply]
  exact Category.comp_id _

/-- The actual tensor left unit sends pure tensor sections to scalar multiples. -/
theorem tensorUnit_section {X : Scheme} (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    (tensorUnit M).hom.app U (tensorSection (unit X) M U r s) = r • s := by
  have hh := congrArg (fun h => h.app (Opposite.op U) (r ⊗ₜ[Γ(X, U)] s))
    (tensorUnit_adjunct M)
  exact hh

/-- The actual tensor left unit is natural for module morphisms. -/
theorem tensorUnit_naturality {X : Scheme} {M N : X.Modules} (f : M ⟶ N) :
    tensorMap (𝟙 (unit X)) f ≫ (tensorUnit N).hom = (tensorUnit M).hom ≫ f := by
  apply tensor_hom_ext
  intro U r s
  change (tensorUnit N).hom.app U
      ((tensorMap (𝟙 (unit X)) f).app U (tensorSection (unit X) M U r s)) =
    f.app U ((tensorUnit M).hom.app U (tensorSection (unit X) M U r s))
  rw [tensorMap_section, tensorUnit_section, tensorUnit_section]
  exact (Scheme.Modules.Hom.app_smul f (show Γ(X, U) from r) s).symm

/-- The inverse tensor left unit sends a section to its pure tensor with one. -/
theorem tensorUnit_inv_section {X : Scheme} (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (tensorUnit M).inv.app U s = tensorSection (unit X) M U (1 : Γ(X, U)) s := by
  have hh := congrArg (fun h : tensor (unit X) M ⟶ tensor (unit X) M =>
    h.app U (tensorSection (unit X) M U (1 : Γ(X, U)) s)) (tensorUnit M).hom_inv_id
  change (tensorUnit M).inv.app U
      ((tensorUnit M).hom.app U (tensorSection (unit X) M U (1 : Γ(X, U)) s)) =
    tensorSection (unit X) M U (1 : Γ(X, U)) s at hh
  rw [tensorUnit_section, one_smul] at hh
  exact hh

end HodgeLean.Foundations.Curves.Picard.LineBundles
