import HodgeLean.Foundations.BundleResolution.ModuleUnitPullbackHelpers

/-! # Coherence between module restriction and pullback -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.TubularEuler

/-- The restriction composition comparison is paired with pushforward composition. -/
theorem moduleRestrictionComp_mate {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
      ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f))
      (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).hom := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x))) = x
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change M.presheaf.map (𝟙 _) x = x
  exact CategoryTheory.congr_fun (M.presheaf.map_id _) x

/-- Uniqueness of a left adjoint is paired with the identity on the right adjoint. -/
theorem moduleLeftAdjointUniq_mate
    {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R) :
    conjugateEquiv adj' adj (adj.leftAdjointUniq adj').hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq]

/-- The restriction/pullback comparison is paired with the unchanged pushforward. -/
theorem moduleRestrictionPullback_mate {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).hom =
        𝟙 (Scheme.Modules.pushforward f) :=
  moduleLeftAdjointUniq_mate _ _

/-- The two successive restriction/pullback comparisons have identity mate. -/
theorem moduleRestrictionPullback_pair_mate {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f))
      (whiskerRight (Scheme.Modules.restrictFunctorIsoPullback g).hom
          (Scheme.Modules.restrictFunctor f) ≫
        whiskerLeft (Scheme.Modules.pullback g) (Scheme.Modules.restrictFunctorIsoPullback f).hom) =
      𝟙 (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g) := by
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.restrictAdjunction f)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    moduleRestrictionPullback_mate f, moduleRestrictionPullback_mate g]
  simp only [whiskerRight_id', whiskerLeft_id', Category.id_comp]

/-- Restriction/pullback comparison respects composition of open immersions. -/
theorem moduleRestrictionPullback_comp {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom ≫
        (Scheme.Modules.pullbackComp f g).inv =
      (Scheme.Modules.restrictFunctorComp f g).hom ≫
        whiskerRight (Scheme.Modules.restrictFunctorIsoPullback g).hom
          (Scheme.Modules.restrictFunctor f) ≫
        whiskerLeft (Scheme.Modules.pullback g) (Scheme.Modules.restrictFunctorIsoPullback f).hom := by
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.restrictAdjunction (f ≫ g))).injective
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) _,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    moduleRestrictionPullback_mate (f ≫ g), Category.comp_id]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)) _,
    moduleRestrictionPullback_pair_mate f g, moduleRestrictionComp_mate f g, Category.id_comp]

/-- Restriction along reflexively equal maps has the identity comparison. -/
theorem moduleRestrictionCongr_refl {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom =
      𝟙 (Scheme.Modules.restrictFunctor f) := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change M.presheaf.map (𝟙 _) x = x
  exact CategoryTheory.congr_fun (M.presheaf.map_id _) x

/-- Restriction/pullback comparison respects equality of open-immersion maps. -/
theorem moduleRestrictionPullback_congr {X Y : Scheme.{0}}
    (f g : X ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    (Scheme.Modules.restrictFunctorCongr h).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).hom =
      (Scheme.Modules.restrictFunctorIsoPullback f).hom ≫
        (Scheme.Modules.pullbackCongr h).hom := by
  subst g
  rw [moduleRestrictionCongr_refl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

/-- Opposite restriction equality comparisons cancel. -/
theorem moduleRestrictionCongr_symm_comp {X Y : Scheme.{0}}
    (f g : X ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    (Scheme.Modules.restrictFunctorCongr h.symm).hom ≫
        (Scheme.Modules.restrictFunctorCongr h).hom =
      𝟙 (Scheme.Modules.restrictFunctor g) := by
  subst g
  rw [moduleRestrictionCongr_refl, Category.id_comp]

end HodgeLean.Foundations.TubularEuler
