import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadCapHomology

/-! # Actual relative-to-triad cap compatibility without representatives
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- For every original relative cohomology class, projecting its relative cap modulo any second subspace gives the original triad cap on the literal quotient homology class.
Source: properCycle_relative_triad_cap_homology; relativeCapCohomologyLinear_on_cycle; triadCapCohomologyLinear_on_cycle.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triad_cap_cohomology
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) (p+q)) :
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) A) p q a c) =
      triadCapCohomologyLinear ℚ X A B p q a
        ((HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map X A B)
          (p+q)).hom c) := by
  let P := TopPair.ofSubset (X := X) A
  let S := ((relativeChainFunctor ℚ).obj P).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ P p).surjective a
  obtain ⟨φ, rfl⟩ := S.linearDual.moduleCatHomologyClass_surjective u
  have hr : relativeCapCohomologyLinear ℚ P p q
      (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ)) =
      relativeCohomologyCycleCapLinear ℚ P p q φ := relativeCapCohomologyLinear_on_cycle ℚ P p q φ
  have ht : triadCapCohomologyLinear ℚ X A B p q
      (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ)) =
      triadRelativeCohomologyCycleCapLinear ℚ X A B p q φ :=
    triadCapCohomologyLinear_on_cycle ℚ X A B p q φ
  rw [hr, ht]
  exact properCycle_relative_triad_cap_homology X A B p q
    (relativeCohomologyCycleToCocycle ℚ P p φ).1
    (relativeCohomologyCycleToCocycle ℚ P p φ).2 c

end HodgeLean.Foundations.QuotientDuality
