import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapCover
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeForgetCochain

/-! # Original relative cap projection vanishing without representatives -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- For an actual two-open cover every relative class has an ordinary cap image with zero literal projection modulo the second open, independently of representatives.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative cap products and excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_projection_zero_relative_cohomology
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p)
    (c : Homology ℚ X (p + q)) :
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm
          (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (X := X) A) p a)) c) = 0 := by
  let P := TopPair.ofSubset (X := X) A
  let S := ((relativeChainFunctor ℚ).obj P).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ P p).surjective a
  obtain ⟨φ, rfl⟩ := S.linearDual.moduleCatHomologyClass_surjective u
  have hpull : (cochainCohomologyEquiv ℚ X p).symm
      (relativeCohomologyToAbsolute ℚ P p
        (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ))) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
          (relativeChainProjection ℚ P)))).hom (S.linearDual.moduleCatHomologyClass φ) :=
    properCycle_relative_forget_cochain_comparison P p _
  refine (congrArg (fun z : CochainCohomology ℚ X p =>
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (capCohomologyLinear ℚ X p q z c)) hpull).trans ?_
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
    (relativeChainProjection ℚ P)
  let τ : LinearMap.ker (((SingularChainComplex ℚ X).sc p).linearDual.g.hom) :=
    ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) φ
  change (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
    (capCohomologyLinear ℚ X p q
      (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyClass τ) c) = 0
  have hcap : capCohomologyLinear ℚ X p q
      (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyClass τ) =
      capHomologyMap ℚ X p q (AlgebraicTopology.Simplicial.cohomologyCycleToCocycle ℚ p τ) :=
    AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle ℚ p q τ
  refine (congrArg (fun f : Homology ℚ X (p + q) →ₗ[ℚ] Homology ℚ X q =>
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom (f c)) hcap).trans ?_
  exact properCycle_cap_projection_zero_of_open_cover X A B hA hB hcover p q
    (relativeCohomologyCycleToCocycle ℚ P p φ).1
    (relativeCohomologyCycleToCocycle ℚ P p φ).2 c

end HodgeLean.Foundations.QuotientDuality
