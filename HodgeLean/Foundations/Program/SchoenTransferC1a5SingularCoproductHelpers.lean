import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! Singular simplices of topological coproducts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Singular simplices retain the actual disjoint-union coproduct cocone.
Source: Mathlib ContinuousMap.exists_lift_sigma; Hatcher §2.1, disjoint unions. -/
def c1a5_singular_sigma_isColimit {I : Type} (X : I → TopCat.{0}) :
    IsColimit (TopCat.toSSet.mapCocone (TopCat.sigmaCofan X)) := by
  refine (isColimitMapCoconeCofanMkEquiv TopCat.toSSet X (TopCat.sigmaι X)).symm ?_
  apply evaluationJointlyReflectsColimits
  intro n
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj n)
    (fun i ↦ TopCat.toSSet.obj (X i)) (fun i ↦ TopCat.toSSet.map (TopCat.sigmaι X i))).symm ?_
  apply Classical.choice
  change Nonempty (IsColimit (Cofan.mk
    ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
    (fun i ↦ (TopCat.toSSet.map (TopCat.sigmaι X i)).app n)))
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma]
  let e := (Equiv.sigmaCongrRight (fun i ↦ TopCat.toSSetObjEquiv (X i) n)).trans
    (ContinuousMap.sigmaCodHomeomorph
      (Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) (fun i ↦ X i)).symm.toEquiv
  convert (e.trans (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n).symm).bijective using 1
  · rfl
  · rfl

/-- The singular simplicial-set functor preserves coproducts with arbitrary small index type.
Source: Mathlib ContinuousMap.sigmaCodHomeomorph and TopCat.sigmaCofanIsColimit. -/
instance c1a5_toSSet_preserves_coproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I) TopCat.toSSet.{0} := by
  have (X : I → TopCat.{0}) : PreservesColimit (Discrete.functor X) TopCat.toSSet :=
    preservesColimit_of_preserves_colimit_cocone (TopCat.sigmaCofanIsColimit X)
      (c1a5_singular_sigma_isColimit X)
  exact preservesColimitsOfShape_of_discrete _

end HodgeLean.Foundations.Program
