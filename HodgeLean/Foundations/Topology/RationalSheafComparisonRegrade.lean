import HodgeLean.Foundations.Topology.RationalSheafComparisonCohomologyNaturality
import HodgeLean.Foundations.Topology.RationalSheafComparisonGlobalNaturality
import HodgeLean.Foundations.Topology.RationalSheafComparisonExtend

/-! Regrading the global resolution pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem globalResolutionPullback_regrade {X Y : TopCat.{0}} (f : X ⟶ Y) :
    globalResolutionPullback f ≫
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X)
        (resolution X).cocomplex ComplexShape.embeddingUpNat).hom =
    (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y)
        (resolution Y).cocomplex ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (globalResolutionPullbackNat f) ComplexShape.embeddingUpNat := by
  unfold globalResolutionPullback resolutionPullbackMapInt globalResolutionPullbackNat
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality]
  rw [← Category.assoc _ _ (HomologicalComplex.extendMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
      (resolutionPullbackMap f)) ComplexShape.embeddingUpNat)]
  rw [← mapExtendCanonicalIso_comp]
  rw [← Category.assoc]
  erw [HomologicalComplex.mapExtendCanonicalIso_natTrans
    (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y)
    (resolution Y).cocomplex ComplexShape.embeddingUpNat (globalInverseImageUnit f)]
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp]
  rfl

end HodgeLean.Topology.RationalSheafComparison
