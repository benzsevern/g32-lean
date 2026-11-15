import HodgeLean.Foundations.Topology.RationalSheafComparisonFunctorial

/-! Uniqueness of maps from a resolution into an injective complex.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Topology.RationalSheafComparison

universe u v

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def homotopyOfEqualAugmentations {C : Type u} [Category.{v} C] [Abelian C]
    {A K I : CochainComplex C ℤ} [I.IsKInjective]
    (a : A ⟶ K) [QuasiIso a] (f g : K ⟶ I) (h : a ≫ f = a ≫ g) :
    Homotopy f g := by
  letI := HasDerivedCategory.standard C
  have hd : DerivedCategory.Q.map f = DerivedCategory.Q.map g := by
    apply (cancel_epi (DerivedCategory.Q.map a)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ I).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, hd]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem homologyMap_eq_of_equal_augmentations
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {A K I : CochainComplex C ℤ} [I.IsKInjective]
    (a : A ⟶ K) [QuasiIso a] (f g : K ⟶ I) (h : a ≫ f = a ≫ g) (n : ℤ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) n :=
  (F.mapHomotopy (homotopyOfEqualAugmentations a f g h)).homologyMap_eq n

section PullbackResolution

open TopologicalSpace
variable {X Y : TopCat.{0}} (f : X ⟶ Y)


/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def resolutionPullbackAugmentation :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj ((CochainComplex.single₀ _).obj (constants Y)) ⟶ (resolution X).cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (.up ℕ) 0).hom.app (constants Y) ≫
    (CochainComplex.single₀ _).map (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom ≫
      (resolution X).ι

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def resolutionPullbackMap : ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj (resolution Y).cocomplex ⟶ (resolution X).cocomplex := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := pullback_preservesFiniteLimits f
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive := pullback_additive f
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  let a := ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map (resolution Y).ι
  haveI : Mono a := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map ((resolution Y).ι.f n))
    infer_instance
  haveI : QuasiIso a := inferInstance
  exact CochainComplex.liftToInjectiveNat a (resolutionPullbackAugmentation f)
    (resolution X).injective

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionPullbackMap_augmentation :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map (resolution Y).ι ≫ resolutionPullbackMap f = resolutionPullbackAugmentation f := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := pullback_preservesFiniteLimits f
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive := pullback_additive f
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  letI : Mono (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
      (resolution Y).ι) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map ((resolution Y).ι.f n))
    infer_instance
  dsimp only [resolutionPullbackMap]
  exact CochainComplex.comp_liftToInjectiveNat _ _ _

/-- Source: Bredon, Sheaf Theory, second edition, III.1. -/
def singularInverseImagePullback :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y) ⟶
        AlgebraicTopology.Singular.singularCochainSheafComplex ℚ X where
  f n := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm
    (HodgeLean.Foundations.Program.singularCochainSheafPullback ℚ f n)
  comm' i j _ := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).injective
    change _ = (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y).d i j) ≫ _)
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hc := (HodgeLean.Foundations.Program.singularCochainSheafComplexPullback ℚ f).comm i j
    change HodgeLean.Foundations.Program.singularCochainSheafPullback ℚ f i ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℚ X).d i j) =
      (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y).d i j ≫
        HodgeLean.Foundations.Program.singularCochainSheafPullback ℚ f j at hc
    simpa only [Equiv.apply_symm_apply] using hc

/-- Source: Bredon, Sheaf Theory, second edition, III.1. -/
theorem singularInverseImagePullback_augmentation :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ Y) ≫
      singularInverseImagePullback f =
    (HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (.up ℕ) 0).hom.app (constants Y) ≫
      (CochainComplex.single₀ _).map (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom ≫
        AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ X := by
  apply (cancel_epi ((HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (.up ℕ) 0).inv.app (constants Y))).mp
  rw [Iso.inv_hom_id_app_assoc]
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map
      (AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℚ Y) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm
        (HodgeLean.Foundations.Program.singularCochainSheafPullback ℚ f 0) =
    (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom ≫
      AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℚ X
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, pullbackConstantsIso_hom_adjunct]
  exact singularPullback_constants f

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
theorem singularResolutionPullback_augmentation
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ Y) ≫
      (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Singular.singularToConstantInjectiveResolution Y hY) ≫
          resolutionPullbackMap f) =
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ Y) ≫
      (singularInverseImagePullback f ≫
        AlgebraicTopology.Singular.singularToConstantInjectiveResolution X hX) := by
  rw [← Category.assoc, ← Functor.map_comp,
    AlgebraicTopology.Singular.constants_comp_singularToConstantInjectiveResolution,
    resolutionPullbackMap_augmentation]
  rw [← Category.assoc, singularInverseImagePullback_augmentation,
    Category.assoc, Category.assoc,
    AlgebraicTopology.Singular.constants_comp_singularToConstantInjectiveResolution]
  rfl

end PullbackResolution

end HodgeLean.Topology.RationalSheafComparison
