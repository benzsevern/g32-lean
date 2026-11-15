import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap

/-! # Composition of the natural ideal comparisons
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- Transposition through the composition isomorphism agrees with iterated transposition. -/
lemma pullbackComp_inv_transpose
    {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (a : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        ((Scheme.Modules.pullbackComp f g).inv.app M ≫ a) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app N := by
  let c := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hu := unit_conjugateEquiv c d (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu, Category.assoc]
  change c.unit.app M ≫ _ = c.homEquiv M N a ≫ _
  calc
    _ = c.unit.app M ≫ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).map a ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N :=
      congrArg (fun t => c.unit.app M ≫ t)
        ((Scheme.Modules.pushforwardComp f g).hom.naturality a).symm
    _ = _ := by rw [Adjunction.homEquiv_unit, Category.assoc]

/-- The natural ideal maps before scalar extension compose. -/
lemma idealPushforwardMap_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f)) :
    idealPushforwardMap i₀ i₁ f g h ≫
        (Scheme.Modules.pushforward f).map (idealPushforwardMap i₁ i₂ f' g' h') ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app (idealModule i₂) =
      idealPushforwardMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'' := by
  let j₂ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i₂.toRingCatSheafHom)
  have : Mono ((Scheme.Modules.pushforward (f' ≫ f)).map j₂) := inferInstance
  apply (cancel_mono ((Scheme.Modules.pushforward (f' ≫ f)).map j₂)).mp
  let j₀ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i₀.toRingCatSheafHom)
  let j₁ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i₁.toRingCatSheafHom)
  let η := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let η' := SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom
  calc
    _ = idealPushforwardMap i₀ i₁ f g h ≫
        (Scheme.Modules.pushforward f).map
          (idealPushforwardMap i₁ i₂ f' g' h' ≫ (Scheme.Modules.pushforward f').map j₂) ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app _ := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun t => idealPushforwardMap i₀ i₁ f g h ≫
        (Scheme.Modules.pushforward f).map (idealPushforwardMap i₁ i₂ f' g' h') ≫ t)
        ((Scheme.Modules.pushforwardComp f' f).hom.naturality j₂).symm
    _ = idealPushforwardMap i₀ i₁ f g h ≫
        (Scheme.Modules.pushforward f).map (j₁ ≫ η') ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app _ := by
      rw [idealPushforwardMap_inclusion]
    _ = (idealPushforwardMap i₀ i₁ f g h ≫ (Scheme.Modules.pushforward f).map j₁) ≫
        (Scheme.Modules.pushforward f).map η' ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app _ := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (j₀ ≫ η) ≫ (Scheme.Modules.pushforward f).map η' ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app _ := by
      rw [idealPushforwardMap_inclusion]
    _ = j₀ ≫ SheafOfModules.unitToPushforwardObjUnit (f' ≫ f).toRingCatSheafHom := by
      rw [Category.assoc, s2e_structureModule_map_comp]
    _ = _ := (idealPushforwardMap_inclusion i₀ i₂ (f' ≫ f) (g' ≫ g) h'').symm

/-- Scalar-extended ideal comparisons compose through the pullback composition isomorphism. -/
lemma idealPullbackMap_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f)) :
    (Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
        (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
        idealPullbackMap i₁ i₂ f' g' h' =
      idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'' := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)).homEquiv _ _).injective
  erw [pullbackComp_inv_transpose]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [idealPullbackMap, Equiv.apply_symm_apply]
  exact idealPushforwardMap_comp i₀ i₁ i₂ f f' g g' h h' h''

end AlgebraicGeometry.Conormal
