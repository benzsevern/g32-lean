import HodgeLean.Foundations.Singular.RationalDualComparison
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! The actual short-complex map underlying rational dual homotopy transport. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Dual homotopy transport is the homology map of the actual reversed-dual short-complex map.
Source: Hatcher, Algebraic Topology, §3.1, naturality of induced cohomology maps. -/
theorem rationalDualCohomologyHomotopyEquiv_map {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (e : HomotopyEquiv K L) (n : ℕ) :
    (rationalDualCohomologyHomotopyEquiv e n).toLinearMap =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map e.hom))).hom := by
  let A := ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso K n)
  let B := ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso L n)
  let f := HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap e.hom) n
  let g := ShortComplex.homologyMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map e.hom))
  have hn : f ≫ A.hom = B.hom ≫ g := by
    have h := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
      (HomologicalComplex.linearDualCochainComplexScIso_naturality e.hom n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have he : B.inv ≫ f ≫ A.hom = g := by
    calc
      _ = B.inv ≫ (B.hom ≫ g) := congrArg (fun k => B.inv ≫ k) hn
      _ = g := by rw [← Category.assoc, B.inv_hom_id, Category.id_comp]
  change (B.inv ≫ f ≫ A.hom).hom = g.hom
  exact congrArg ModuleCat.Hom.hom he

/-- Reversing the actual chain homotopy equivalence reverses its dual-cohomology transport.
Source: Hatcher, Algebraic Topology, §3.1, induced cohomology equivalences. -/
theorem rationalDualCohomologyHomotopyEquiv_symm {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (e : HomotopyEquiv K L) (n : ℕ) :
    (rationalDualCohomologyHomotopyEquiv e n).symm =
      rationalDualCohomologyHomotopyEquiv e.symm n := by
  rfl

#print axioms rationalDualCohomologyHomotopyEquiv_symm
#print axioms rationalDualCohomologyHomotopyEquiv_map
end HodgeLean.Foundations.Singular
