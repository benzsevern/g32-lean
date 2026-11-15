import HodgeLean.Foundations.Algebraic.GrassmannianSheafQuot

/-! # Grassmannian sheaf lane: restriction of sheaves of modules to opens

Restriction along an open immersion `j : V ⟶ T` preserves all limits, in particular kernels and
products: on underlying presheaves of abelian groups it is precomposition with the open
functor of `j`. Restriction sends free sheaves to free sheaves (`f5sheaf_restrictFreeIso`), and
the restriction of the morphism of a matrix `Y` is the morphism of the matrix with entries
restricted by `j.appTop`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Algebraic

set_option backward.isDefEq.respectTransparency false

variable {V T : Scheme.{0}} (j : V ⟶ T) [IsOpenImmersion j]

/-! ### Restriction preserves limits -/

/-- On underlying presheaves of abelian groups, restriction along an open immersion is
precomposition with its open functor.
Source: EGA 0_I, §4.1.7 (restriction of a sheaf to an open). -/
def f5sheaf_restrictToPresheafIso :
    Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf V ≅
      Scheme.Modules.toPresheaf T ⋙ (Functor.whiskeringLeft _ _ _).obj j.opensFunctor.op :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

instance f5sheaf_restrict_preservesLimits :
    PreservesLimits (Scheme.Modules.restrictFunctor j) := by
  have : PreservesLimits ((Functor.whiskeringLeft _ _ Ab).obj j.opensFunctor.op) :=
    ⟨fun {_} _ => inferInstance⟩
  have : PreservesLimits (Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf V) :=
    preservesLimits_of_natIso (f5sheaf_restrictToPresheafIso j).symm
  have : ReflectsLimits (Scheme.Modules.toPresheaf V) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf V)


/-! ### Restriction of free sheaves and matrices -/

instance f5sheaf_restrict_preservesColimits :
    PreservesColimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor j) :=
  (Scheme.Modules.restrictAdjunction j).leftAdjoint_preservesColimits

instance f5sheaf_restrict_preservesColimitsOfShape (I : Type) :
    @PreservesColimitsOfShape (SheafOfModules.{0} T.ringCatSheaf) SheafOfModules.instCategory
      (SheafOfModules.{0} V.ringCatSheaf) SheafOfModules.instCategory (Discrete I) _
      (Scheme.Modules.restrictFunctor j) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Scheme.Modules.restrictFunctor j))

/-- The restriction of the free sheaf on `I` along an open immersion is the free sheaf on `I`.
Source: Mathlib `SheafOfModules.mapFreeIso`, `Scheme.Modules.restrictUnitIso`; EGA 0_I, §5.4.1. -/
def f5sheaf_restrictFreeIso (I : Type) :
    f5sheaf_free V I ≅ (Scheme.Modules.restrictFunctor j).obj (f5sheaf_free T I) :=
  SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor j) I
    (Scheme.Modules.restrictUnitIso j).symm

@[reassoc]
theorem f5sheaf_ιFree_restrictFreeIso_hom {I : Type} (i : I) :
    f5sheaf_ιFree i ≫ (f5sheaf_restrictFreeIso j I).hom =
      (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map (f5sheaf_ιFree i) :=
  SheafOfModules.ιFree_mapFreeIso_hom (Scheme.Modules.restrictFunctor j) I
    (Scheme.Modules.restrictUnitIso j).symm i

theorem f5sheaf_appIso_hom_res (W : V.Opens) (a : Γ(T, ⊤)) :
    (j.appIso W).hom (T.presheaf.map (homOfLE le_top).op a) =
      V.presheaf.map (homOfLE le_top).op (j.appTop a) := by
  rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, ← CommRingCat.comp_apply (T.presheaf.map _),
    j.naturality, CommRingCat.comp_apply, ← CommRingCat.comp_apply (V.presheaf.map _),
    ← Functor.map_comp]
  rfl

theorem f5sheaf_restrict_scal (a : Γ(T, ⊤)) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map (f5sheaf_scal a) ≫
          (Scheme.Modules.restrictUnitIso j).hom =
      f5sheaf_scal (j.appTop a) := by
  apply f5sheaf_unit_hom_ext
  intro W
  change (j.appIso W.unop).hom ((j.appIso W.unop).inv (1 : Γ(V, W.unop)) *
    T.presheaf.map (homOfLE le_top).op a) = (1 : Γ(V, W.unop)) * _
  rw [map_mul, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    f5sheaf_appIso_hom_res]
  rfl


section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

instance f5sheaf_restrict_additive : (Scheme.Modules.restrictFunctor j).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end

theorem f5sheaf_restrict_map_sum {M N : T.Modules} {ι : Type*}
    (s : Finset ι) (f : ι → (M ⟶ N)) :
    (Scheme.Modules.restrictFunctor j).map (∑ i ∈ s, f i) =
      ∑ i ∈ s, (Scheme.Modules.restrictFunctor j).map (f i) :=
  Functor.map_sum (Scheme.Modules.restrictFunctor j) f s

theorem f5sheaf_restrict_scal' (a : Γ(T, ⊤)) :
    f5sheaf_scal (j.appTop a) ≫ (Scheme.Modules.restrictUnitIso j).inv =
      (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map (f5sheaf_scal a) := by
  rw [← f5sheaf_restrict_scal, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem f5sheaf_restrict_matHom {ι κ : Type} [Fintype κ] (Y : Matrix κ ι Γ(T, ⊤)) :
    (f5sheaf_restrictFreeIso j ι).hom ≫ (Scheme.Modules.restrictFunctor j).map (f5sheaf_matHom Y) =
      f5sheaf_matHom (f5sheaf_matPullback j Y) ≫ (f5sheaf_restrictFreeIso j κ).hom := by
  apply f5sheaf_free_hom_ext
  intro i
  rw [f5sheaf_ιFree_restrictFreeIso_hom_assoc, ← Functor.map_comp, f5sheaf_ιFree_matHom,
    f5sheaf_ιFree_matHom_assoc, f5sheaf_restrict_map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Category.assoc, f5sheaf_ιFree_restrictFreeIso_hom, ← Category.assoc,
    f5sheaf_matPullback, Matrix.map_apply, f5sheaf_restrict_scal', Category.assoc,
    Functor.map_comp]

end HodgeLean.Foundations.Algebraic
