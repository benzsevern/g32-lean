import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Algebra.Homology.QuasiIso

/-! Singular-chain equivalences supplied by actual deformation retractions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual retraction and its specified homotopy give inverse singular-chain maps. -/
def persistenceRetractionSingularChainHomotopyEquiv
    (K : Type) [CommRing K] (A U : TopCat.{0}) (j : A ⟶ U) (q : U ⟶ A)
    (hq : j ≫ q = 𝟙 A) (H : TopCat.Homotopy (𝟙 U) (q ≫ j)) :
    HomotopyEquiv (SingularChainComplex K A) (SingularChainComplex K U) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
    (ModuleCat.{0} K)).obj (ModuleCat.of K K)
  exact {
    hom := F.map j
    inv := F.map q
    homotopyHomInvId := Homotopy.ofEq (by rw [← F.map_comp, hq, F.map_id])
    homotopyInvHomId :=
      (Homotopy.ofEq (F.map_comp q j).symm).trans
        ((TopCat.Homotopy.singularChainComplexFunctorObjMap
          (f := q ≫ j) (g := 𝟙 U) H.symm (ModuleCat.of K K)).trans
          (Homotopy.ofEq (F.map_id U))) }

end HodgeLean.Foundations.QuotientDuality
