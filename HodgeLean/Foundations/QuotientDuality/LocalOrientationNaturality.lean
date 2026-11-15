import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! Naturality of localization to a point complement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem relativeHomologyProjection_map {A B : TopPair.{0}} (n : ℕ)
    (F : A ⟶ B) (c : Homology ℚ A.fst n) :
    relativeHomologyMap ℚ n F ((relativeHomologyProjection ℚ A n).hom c) =
      (relativeHomologyProjection ℚ B n).hom (homologyMap ℚ n F.hom.right c) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) F)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

theorem localOrientation_map {X Y : TopCat.{0}} (n : ℕ)
    (x : X) (y : Y) (F : pointComplementPair x ⟶ pointComplementPair y)
    (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n F (localOrientation X n c x) =
      localOrientation Y n (homologyMap ℚ n F.hom.right c) y := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) F)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

#print axioms localOrientation_map
end HodgeLean.Foundations.QuotientDuality
