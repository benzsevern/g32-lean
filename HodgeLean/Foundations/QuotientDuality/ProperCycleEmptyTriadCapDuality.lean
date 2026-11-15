import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadCap

/-! # Original cap duality at the empty-triad base case -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original same-pair cap bijectivity supplies the original empty-triad cap base case for the same actual relative cohomology class.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_triad_cohomology_cap_bijective
    (X : TopCat.{0}) (A : Set X) (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p)
    (hc : Function.Bijective (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) A) p q a)) :
    Function.Bijective (triadCapCohomologyLinear ℚ X A ∅ p q a) := by
  let C := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p).surjective a
  obtain ⟨φ, rfl⟩ := C.linearDual.moduleCatHomologyClass_surjective u
  erw [relativeCapCohomologyLinear_on_cycle] at hc
  erw [triadCapCohomologyLinear_on_cycle]
  let ψ := relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ
  let F := HomologicalComplex.homologyMap (properCycle_empty_triad_relative_iso X A).hom (p + q)
  let G := HomologicalComplex.homologyMap
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) q
  letI := properCycle_empty_relative_projection_isIso X
  have h := (ConcreteCategory.bijective_of_isIso G).comp
    (hc.comp (ConcreteCategory.bijective_of_isIso F))
  change Function.Bijective ((F ≫ ModuleCat.ofHom
    (relativeCapHomologyMap ℚ (TopPair.ofSubset (X := X) A) p q ψ.1 ψ.2) ≫ G).hom) at h
  dsimp only [F, G] at h
  rw [properCycle_empty_triad_cap_homology_comparison X A p q hp ψ.1 ψ.2] at h
  exact h

/-- The specified original standard complex normal coclass supplies bijectivity of the actual empty-triad cap base case.
Source: Hatcher, Algebraic Topology, section 3.3, complex normal orientations and relative cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_normal_triad_cap_bijective (d : ℕ) :
    Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (Fin d → ℂ))
      ({0} : Set (Fin d → ℂ))ᶜ ∅ (2 * d) 0
      (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
        (standardComplexLocalClass_ne_zero_for_chart d))) := by
  apply properCycle_empty_triad_cohomology_cap_bijective _ _ (2 * d) 0
    (by exact ⟨d, by omega⟩)
  exact properCycle_standard_normal_cap_bijective d

end HodgeLean.Foundations.QuotientDuality
