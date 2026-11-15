import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing

/-! Degree-zero orientations and the absolute class on a singleton space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- A degree-zero local orientation on a path-connected space forces a singleton.
Source: Hatcher, Algebraic Topology, section 2.1, relative degree-zero homology. -/
theorem subsingleton_of_zero_orientation (X : TopCat.{0}) [PathConnectedSpace X]
    (o : LocalRationalOrientation X 0) : Subsingleton X := by
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  letI : Nonempty (pointComplementPair x).snd :=
    ⟨⟨y, fun hy => hxy (Set.mem_singleton_iff.mp hy).symm⟩⟩
  letI : PathConnectedSpace (pointComplementPair x).fst :=
    inferInstanceAs (PathConnectedSpace X)
  letI := ModuleCat.subsingleton_of_isZero
    (relativeHomology_zero_isZero_of_pathConnected (pointComplementPair x))
  have hg : o.generator x = 0 := Subsingleton.elim _ _
  have h01 : (0 : ℚ) = 1 := (o.generates x).1 (by
    simp only [LinearMap.toSpanSingleton_apply, hg, smul_zero])
  exact zero_ne_one h01

/-- On a singleton, the actual local projection determines a unique absolute class.
Source: Hatcher, Algebraic Topology, section 2.1, homology relative to the empty subspace. -/
theorem singleton_fundamental_class (X : TopCat.{0}) [Nonempty X] [Subsingleton X]
    (n : ℕ) (o : LocalRationalOrientation X n) :
    ∃! c : Homology ℚ X n, ∀ x, localOrientation X n c x = o.generator x := by
  let x : X := Classical.choice inferInstance
  let P := pointComplementPair x
  letI : IsIso (relativeChainProjection ℚ P) := isIso_relativeChainProjection _
    ⟨fun y => y.property (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))⟩
  letI : IsIso (relativeHomologyProjection ℚ P n) := by
    unfold relativeHomologyProjection
    infer_instance
  have hp : Function.Bijective (relativeHomologyProjection ℚ P n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  obtain ⟨c, hc⟩ := hp.2 (o.generator x)
  have hlocal : ∀ y, localOrientation X n c y = o.generator y := by
    intro y
    have hy : y = x := Subsingleton.elim _ _
    subst y
    exact hc
  refine ⟨c, hlocal, fun c' hc' => hp.1 ?_⟩
  exact (hc' x).trans hc.symm

#print axioms singleton_fundamental_class

#print axioms subsingleton_of_zero_orientation
end HodgeLean.Foundations.QuotientDuality
