import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Contractible
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffinePrism
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Rational cycle fillers for the universal simplex-product models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.Singular

/-- The actual rational singular chain complex of a topological space.
Source: Hatcher, Algebraic Topology, §2.1, singular chains with rational coefficients. -/
abbrev rationalChains (X : TopCat.{0}) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj X

/-- Every positive-degree rational cycle in a contractible space has a singular-chain filler.
Source: Hatcher, Algebraic Topology, Theorem 2.10, homotopy invariance. -/
theorem contractible_cycle_filler
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ)
    (z : (rationalChains (TopCat.of X)).X (n + 1))
    (hz : ((rationalChains (TopCat.of X)).d (n + 1) n).hom z = 0) :
    ∃ w : (rationalChains (TopCat.of X)).X (n + 2),
      ((rationalChains (TopCat.of X)).d (n + 2) (n + 1)).hom w = z := by
  have he := singularChainComplex_exactAt_of_contractible ℚ X (n + 1) (by omega)
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)] at he
  have hzker : z ∈ LinearMap.ker
      ((rationalChains (TopCat.of X)).d (n + 1) n).hom := hz
  have hr : LinearMap.range
      ((rationalChains (TopCat.of X)).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((rationalChains (TopCat.of X)).d (n + 1) n).hom :=
    he.moduleCat_range_eq_ker
  rw [← hr] at hzker
  exact hzker

/-- The actual product of two topological standard simplices.
Source: Hatcher, Algebraic Topology, §3.2, the universal product models. -/
abbrev simplexProductModel (p q : ℕ) :=
  Convexity.StdSimplex ℝ (Fin (p + 1)) × Convexity.StdSimplex ℝ (Fin (q + 1))

/-- The standard product models are contractible.
Source: Hatcher, Algebraic Topology, §2.1; convexity of simplices and products of contractions. -/
theorem simplexProductModel_contractible (p q : ℕ) :
    ContractibleSpace (simplexProductModel p q) := by
  letI := AlgebraicTopology.Singular.standardTopologicalSimplex_contractibleSpace p
  letI := AlgebraicTopology.Singular.standardTopologicalSimplex_contractibleSpace q
  infer_instance

/-- Positive rational cycles in each universal simplex-product model have fillers.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic product models. -/
theorem simplexProductModel_cycle_filler (p q n : ℕ)
    (z : (rationalChains (TopCat.of (simplexProductModel p q))).X (n + 1))
    (hz : ((rationalChains (TopCat.of (simplexProductModel p q))).d (n + 1) n).hom z = 0) :
    ∃ w : (rationalChains (TopCat.of (simplexProductModel p q))).X (n + 2),
      ((rationalChains (TopCat.of (simplexProductModel p q))).d (n + 2) (n + 1)).hom w = z := by
  letI := simplexProductModel_contractible p q
  exact contractible_cycle_filler _ n z hz

/-- The contraction to a point supplies a filler for each degree-zero chain
annihilated by the actual point map.
Source: Hatcher, Algebraic Topology, Theorem 2.10, the chain homotopy of a contraction. -/
theorem contractible_zero_cycle_filler
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (z : (rationalChains (TopCat.of X)).X 0)
    (hz : ((contractibleSingularChainHomotopyEquiv ℚ X).hom.f 0).hom z = 0) :
    ∃ w : (rationalChains (TopCat.of X)).X 1,
      ((rationalChains (TopCat.of X)).d 1 0).hom w = z := by
  let e := contractibleSingularChainHomotopyEquiv ℚ X
  let H := e.homotopyHomInvId
  have he := H.comm 0
  rw [dNext_eq_zero H.hom 0 (by simp),
    prevD_eq H.hom (show (ComplexShape.down ℕ).Rel 1 0 by simp),
    zero_add] at he
  have hv := congrArg (fun f => ModuleCat.Hom.hom f z) he
  change (e.inv.f 0).hom ((e.hom.f 0).hom z) =
    ((rationalChains (TopCat.of X)).d 1 0).hom ((H.hom 0 1).hom z) + z at hv
  change (e.hom.f 0).hom z = 0 at hz
  rw [hz, map_zero] at hv
  refine ⟨-(H.hom 0 1).hom z, ?_⟩
  rw [map_neg, eq_neg_of_add_eq_zero_left hv.symm, neg_neg]

#print axioms contractible_zero_cycle_filler
#print axioms simplexProductModel_cycle_filler
#print axioms simplexProductModel_contractible
#print axioms contractible_cycle_filler
end HodgeLean.Foundations.Singular
