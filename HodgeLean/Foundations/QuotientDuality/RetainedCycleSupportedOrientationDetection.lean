import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportedUnitDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedSupportedHomology

/-! # Nonzero detection through the original supported orientation comparison -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance supportedOrientationDetectionSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _
local instance supportedOrientationDetectionGroupDerived : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- A nonzero global image detects the actual supported orientation comparison on ordinary section homology. -/
theorem retained_supported_orientation_homology_nonzero
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N : ℕ) (o : LocalRationalOrientation X (N+1))
    (S : Closeds X) (c : Homology ℚ X (N+1))
    (ho : ∀ x, Function.Bijective (orientationLine X (N+1) c x))
    (hv : ∀ m : ℕ, m ≠ N+1 → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (i : ℤ) (hi : -((N+1 : ℕ) : ℤ)+1 < i)
    (a : (((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj
      (properCycle_bounded_chain_sheaf X (N+1)).obj).homology i)
    (ha : (HomologicalComplex.homologyMap
      (((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (properCycle_bounded_chain_sheaf X (N+1)).obj) i).hom a ≠ 0) :
    (properCycle_bounded_supported_homology_comparison X S (N+1) c ho hv i).hom a ≠ 0 := by
  let K := properCycle_bounded_chain_sheaf X (N+1)
  let F := TopCat.Sheaf.closedSupportSections X S
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat i
  let e := retainedPlusHomologyComparison AddCommGrpCat i
  have hn := retained_supported_raw_unit_nonzero_of_global_image X t N o S i hi a ha
  have he : properCycle_bounded_supported_homology_comparison X S (N+1) c ho hv i =
      e.inv.app (F.mapCochainComplexPlus.obj K) ≫
        H.map (F.rightDerivedFunctorPlusUnit.app K) ≫
          H.map (properCycle_bounded_supported_orientation X S (N+1) c ho hv).hom := by
    simp [e, H, F, K, retainedPlusHomologyComparison,
      properCycle_bounded_supported_homology_comparison,
      properCycle_bounded_supported_section_comparison, Functor.map_comp, Category.assoc]
  rw [he]
  intro hz
  have hinj := (ConcreteCategory.bijective_of_isIso
    (H.map (properCycle_bounded_supported_orientation X S (N+1) c ho hv).hom)).1
  exact hn (hinj (hz.trans (map_zero _).symm))

end HodgeLean.Foundations.QuotientDuality
