import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadCap

/-! # The original empty-triad cap for arbitrary cohomology classes
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original empty-triad cohomology cap retains the actual relative source comparison and empty-relative target projection.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_empty_triad_cap_homology_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_triad_cohomology_cap_comparison
    (X : TopCat.{0}) (A : Set X) (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p) :
    HomologicalComplex.homologyMap (properCycle_empty_triad_relative_iso X A).hom (p+q) ≫
        ModuleCat.ofHom (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) A) p q a) ≫
        HomologicalComplex.homologyMap
          (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) q =
      ModuleCat.ofHom (triadCapCohomologyLinear ℚ X A ∅ p q a) := by
  let C := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p).surjective a
  obtain ⟨φ, rfl⟩ := C.linearDual.moduleCatHomologyClass_surjective u
  erw [relativeCapCohomologyLinear_on_cycle, triadCapCohomologyLinear_on_cycle]
  let ψ := relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ
  exact properCycle_empty_triad_cap_homology_comparison X A p q hp ψ.1 ψ.2

end HodgeLean.Foundations.QuotientDuality
