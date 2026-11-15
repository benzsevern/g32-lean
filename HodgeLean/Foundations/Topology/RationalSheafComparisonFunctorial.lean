import HodgeLean.Foundations.Topology.RationalSheafComparisonNaturality

/-! Functorial properties of inverse image on rational constant cohomology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 8
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Topology.RationalSheafComparison

instance pullback_preservesFiniteLimits {X Y : TopCat.{0}} (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
  letI : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits (Opens.map f)
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) AddCommGrpCat.{0} _ _

instance pullback_additive {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem pullbackConstantsIso_id_hom (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    (pullbackConstantsIso (𝟙 X) A).hom =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (𝟙 X)).counit.app
        ((TopCat.Sheaf.constantFunctor X).obj A) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (𝟙 X)).homEquiv _ _).injective
  rw [pullbackConstantsIso_hom_adjunct, TopCat.Sheaf.constantRestriction_id]
  rw [Adjunction.homEquiv_unit]
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (𝟙 X)).right_triangle_components
    ((TopCat.Sheaf.constantFunctor X).obj A) |>.symm

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem sheafPullback_id (X : TopCat.{0}) (n : ℕ) (v : Sheaf.H (constants X) n) :
    sheafPullback (𝟙 X) n v = v := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} (𝟙 X)) := pullback_preservesFiniteLimits _
  letI : PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 X)) := by
    change PreservesFiniteColimits (𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X))
    infer_instance
  letI : PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 X)) := by
    change PreservesFiniteLimits (𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X))
    infer_instance
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} (𝟙 X)) := inferInstance
  letI : PreservesFiniteLimits (𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X)) := inferInstance
  letI : PreservesFiniteColimits (𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X)) := inferInstance
  letI : (𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  change ((Abelian.Ext.mk₀ (pullbackConstantsIso (𝟙 X) (AddCommGrpCat.of (ULift ℤ))).inv).comp
    (v.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{0} (𝟙 X))) (zero_add n)).comp
      (Abelian.Ext.mk₀ (pullbackConstantsIso (𝟙 X) (AddCommGrpCat.of ℚ)).hom) (add_zero n) = v
  rw [Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)]
  rw [pullbackConstantsIso_id_hom]
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have h := Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 X) ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{0} (𝟙 X))
    (G := 𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X)) v
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (𝟙 X)).counit
  change (v.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{0} (𝟙 X))).comp
      (Abelian.Ext.mk₀ ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (𝟙 X)).counit.app _)) (add_zero n) = _ at h
  rw [h]
  rw [← pullbackConstantsIso_id_hom, ← Abelian.Ext.comp_assoc _ _ _ (add_zero 0)
    (zero_add n) (by omega), Abelian.Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  exact Abelian.Ext.id_mapExactFunctor v

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def pullbackCompositionIso {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{0} g ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{0} f :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (f ≫ g)).leftAdjointUniq
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f))

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem pullbackCompositionIso_constants {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : AddCommGrpCat.{0}) :
    (pullbackCompositionIso f g).hom.app ((TopCat.Sheaf.constantFunctor Z).obj A) ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (pullbackConstantsIso g A).hom ≫
        (pullbackConstantsIso f A).hom = (pullbackConstantsIso (f ≫ g) A).hom := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (f ≫ g)).homEquiv _ _).injective
  rw [pullbackConstantsIso_hom_adjunct]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  dsimp only [pullbackCompositionIso]
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  change _ = TopCat.Sheaf.constantRestriction (f ≫ g) A
  rw [TopCat.Sheaf.constantRestriction_comp]
  rw [Adjunction.comp_unit_app]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
  change (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.app _ ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app _ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (pullbackConstantsIso g A).hom) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (pullbackConstantsIso f A).hom) = _
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit_naturality_assoc]
  rw [CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← Adjunction.homEquiv_unit, pullbackConstantsIso_hom_adjunct]
  simpa only [Adjunction.homEquiv_unit] using congrArg
    (fun k => k ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
      (TopCat.Sheaf.constantRestriction f A)) (pullbackConstantsIso_hom_adjunct g A)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem pullbackCompositionIso_constants_inv {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : AddCommGrpCat.{0}) :
    (pullbackConstantsIso (f ≫ g) A).inv ≫
        (pullbackCompositionIso f g).hom.app ((TopCat.Sheaf.constantFunctor Z).obj A) =
      (pullbackConstantsIso f A).inv ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (pullbackConstantsIso g A).inv := by
  apply (cancel_mono ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map
    (pullbackConstantsIso g A).hom ≫ (pullbackConstantsIso f A).hom)).mp
  simp only [Category.assoc, pullbackCompositionIso_constants,
    Iso.inv_hom_id, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem sheafPullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (v : Sheaf.H (constants Z) n) :
    sheafPullback (f ≫ g) n v = sheafPullback f n (sheafPullback g n v) := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g)) := pullback_preservesFiniteLimits _
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := pullback_preservesFiniteLimits _
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} g) := pullback_preservesFiniteLimits _
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g)).Additive := pullback_additive _
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive := pullback_additive _
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} g).Additive := pullback_additive _
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g)) := inferInstance
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} g) := inferInstance
  have h := Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp
    (F := TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g))
    (G := TopCat.Sheaf.pullback AddCommGrpCat.{0} g ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{0} f) v
    (pullbackCompositionIso f g).hom
  change ((Abelian.Ext.mk₀ (pullbackConstantsIso (f ≫ g) (AddCommGrpCat.of (ULift ℤ))).inv).comp
    (v.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g))) (zero_add n)).comp
      (Abelian.Ext.mk₀ (pullbackConstantsIso (f ≫ g) (AddCommGrpCat.of ℚ)).hom) (add_zero n) =
    ((Abelian.Ext.mk₀ (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv).comp
      ((((Abelian.Ext.mk₀ (pullbackConstantsIso g (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (v.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{0} g)) (zero_add n)).comp
          (Abelian.Ext.mk₀ (pullbackConstantsIso g (AddCommGrpCat.of ℚ)).hom) (add_zero n)).mapExactFunctor
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)) (zero_add n)).comp
      (Abelian.Ext.mk₀ (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom) (add_zero n)
  rw [← pullbackCompositionIso_constants f g (AddCommGrpCat.of ℚ)]
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (by omega), h]
  rw [Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)]
  rw [← Abelian.Ext.comp_assoc _ _ _ (add_zero 0) (zero_add n) (by omega),
    Abelian.Ext.mk₀_comp_mk₀, pullbackCompositionIso_constants_inv]
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_mapExactFunctor]
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

end HodgeLean.Topology.RationalSheafComparison
