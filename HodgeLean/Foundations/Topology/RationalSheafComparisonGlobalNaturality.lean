import HodgeLean.Foundations.Topology.RationalSheafComparisonChainNaturality
import HodgeLean.Foundations.Topology.RationalSheafComparisonSections

/-! Naturality of the ordinary-to-resolution comparison on global cohomology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def globalInverseImageComplexUnitNat {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
        (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj K) where
  f n := (globalInverseImageUnit f).app (K.X n)
  comm' i j _ := ((globalInverseImageUnit f).naturality (K.d i j)).symm

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem globalInverseImageComplexUnitNat_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ} (g : K ⟶ L) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex (.up ℕ)).map g ≫
      globalInverseImageComplexUnitNat f L =
    globalInverseImageComplexUnitNat f K ≫
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
        (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (globalInverseImageUnit f).naturality (g.f n)

/-- Source: Bredon, Sheaf Theory, second edition, III.1. -/
theorem singularGlobalSheafPullback_adjunct {X Y : TopCat.{0}} (f : X ⟶ Y) :
    HodgeLean.Foundations.Program.singularGlobalSheafPullback f =
      globalInverseImageComplexUnitNat f (singularCochainSheafComplex ℚ Y) ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
          (singularInverseImagePullback f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).apply_symm_apply
    (HodgeLean.Foundations.Program.singularCochainSheafPullback ℚ f n)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.hom.app (Opposite.op ⊤)) h.symm

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def globalResolutionPullbackNat {X Y : TopCat.{0}} (f : X ⟶ Y) :=
  globalInverseImageComplexUnitNat f (resolution Y).cocomplex ≫
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
      (resolutionPullbackMap f)

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
theorem comparisonComplex_naturality_homology {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ f) ≫ comparisonComplex X hX) n =
      HomologicalComplex.homologyMap (comparisonComplex Y hY ≫ globalResolutionPullbackNat f) n := by
  have hs := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomotopy
    (Homotopy.ofExtend (singularResolutionPullbackHomotopy f hX hY))).homologyMap_eq n
  unfold comparisonComplex globalResolutionPullbackNat
  rw [← Category.assoc, HodgeLean.Foundations.Program.singularGlobalComparison_naturality,
    Category.assoc, singularGlobalSheafPullback_adjunct]
  simp only [Category.assoc]
  rw [← Category.assoc _ (globalInverseImageComplexUnitNat f (resolution Y).cocomplex) _,
    globalInverseImageComplexUnitNat_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  change HomologicalComplex.homologyMap
    (HodgeLean.Foundations.Program.singularGlobalComparison Y ≫
      globalInverseImageComplexUnitNat f (singularCochainSheafComplex ℚ Y) ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
          (singularRoute f hX)) n = _
  simp only [HomologicalComplex.homologyMap_comp]
  rw [← hs]
  rfl

end HodgeLean.Topology.RationalSheafComparison
