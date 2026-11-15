import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainHomologyCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportedOrientationDetection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleBoundedSupportDetection

/-! # Nonvanishing of the actual supported derived chain class -/

noncomputable section
open CategoryTheory HomologicalComplex TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A singular class with nonzero ambient image has a nonzero original derived supported chain class. -/
theorem retained_derived_support_chain_class_nonzero
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N : ℕ) (o : LocalRationalOrientation X (N+1))
    (S : Closeds X) (c : Homology ℚ X (N+1))
    (ho : ∀ x, Function.Bijective (orientationLine X (N+1) c x))
    (hv : ∀ m : ℕ, m ≠ N+1 → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (n : ℕ) (hi : -((N+1 : ℕ) : ℤ)+1 < -(n : ℤ))
    (z : Homology ℚ (TopCat.of (S : Set X)) n)
    (hz : homologyMap ℚ n (TopPair.ofSubset (X := X) (S : Set X)).map z ≠ 0) :
    (properCycle_derived_support_chain_class_map X S (N+1) c ho hv n).hom z ≠ 0 := by
  let K := SingularChainComplex ℚ (TopCat.of (S : Set X))
  let L := SingularChainComplex ℚ X
  let f : K ⟶ L := ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let G := F.mapHomologicalComplex (.down ℕ)
  let a := (retainedChainHomologyCoordinates K n).inv.hom z
  have hcoord := ConcreteCategory.congr_hom
    (retained_chain_homology_coordinates_naturality f n) z
  simp only [ConcreteCategory.comp_apply] at hcoord
  change (retainedChainHomologyCoordinates L n).inv.hom
      ((F.map (HomologicalComplex.homologyMap f n)).hom z) =
    (HomologicalComplex.homologyMap
      (extendMap (G.map f) ComplexShape.embeddingDownNat) (-(n : ℤ))).hom a at hcoord
  have ha : (HomologicalComplex.homologyMap
      (extendMap (G.map f) ComplexShape.embeddingDownNat) (-(n : ℤ))).hom a ≠ 0 := by
    intro h
    apply hz
    have hinj := (ConcreteCategory.bijective_of_isIso
      (retainedChainHomologyCoordinates L n).inv).1
    exact hinj ((hcoord.trans h).trans (map_zero _).symm)
  have hg := retained_bounded_support_chain_global_nonzero X S (N+1) (-(n : ℤ)) hi a ha
  rw [HomologicalComplex.homologyMap_comp] at hg
  have hn := retained_supported_orientation_homology_nonzero X t N o S c ho hv
    (-(n : ℤ)) hi
    ((HomologicalComplex.homologyMap (properCycle_bounded_support_chain_map X S (N+1))
      (-(n : ℤ))).hom a) hg
  exact hn

/-- The original derived supported chain construction detects ambient nonvanishing throughout its unchanged window. -/
theorem retained_derived_support_chain_class_nonzero_in_window
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (D : ℕ) (o : LocalRationalOrientation X D)
    (S : Closeds X) (c : Homology ℚ X D)
    (ho : ∀ x, Function.Bijective (orientationLine X D c x))
    (hv : ∀ m : ℕ, m ≠ D → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (n : ℕ) (hi : -(D : ℤ)+1 < -(n : ℤ))
    (z : Homology ℚ (TopCat.of (S : Set X)) n)
    (hz : homologyMap ℚ n (TopPair.ofSubset (X := X) (S : Set X)).map z ≠ 0) :
    (properCycle_derived_support_chain_class_map X S D c ho hv n).hom z ≠ 0 := by
  cases D with
  | zero => omega
  | succ N => exact retained_derived_support_chain_class_nonzero X t N o S c ho hv n hi z hz

end HodgeLean.Foundations.QuotientDuality
