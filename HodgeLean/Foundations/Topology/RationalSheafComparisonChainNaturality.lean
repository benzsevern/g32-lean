import HodgeLean.Foundations.Topology.RationalSheafComparisonResolution

/-! The singular resolution square up to homotopy.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  (hX : ∀ (x : X) (U : Opens X), x ∈ U →
    ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
  (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
    ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U)

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
def resolutionRoute :=
  ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
    (singularToConstantInjectiveResolution Y hY) ≫ resolutionPullbackMap f

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
def singularRoute := singularInverseImagePullback f ≫ singularToConstantInjectiveResolution X hX

/-- Source: Bredon, Sheaf Theory, second edition, II.4 and III.1. -/
def singularResolutionPullbackHomotopy :
    Homotopy (HomologicalComplex.extendMap (resolutionRoute f hY) ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap (singularRoute f hX) ComplexShape.embeddingUpNat) := by
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := pullback_preservesFiniteLimits f
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive := pullback_additive f
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  haveI : QuasiIso (constantsToSingularCochainSheafComplex ℚ Y) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hY
  let a := ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
    (constantsToSingularCochainSheafComplex ℚ Y)
  haveI : QuasiIso a := inferInstance
  apply homotopyOfEqualAugmentations (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun k => HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
    (singularResolutionPullback_augmentation f hX hY)

end HodgeLean.Topology.RationalSheafComparison
