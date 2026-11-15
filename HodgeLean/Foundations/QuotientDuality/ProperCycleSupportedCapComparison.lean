import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeForgetCochain

/-! # Original relative cap comparison without representatives -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Projection of an ordinary cap image agrees with the actual relative triad cap pairing for every relative cohomology class.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative cap products and excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_relative_projection_cohomology
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p)
    (c : Homology ℚ X (p + q)) :
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm
          (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (X := X) A) p a)) c) =
      triadCapCohomologyLinear ℚ X A B p q a
        ((HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) (p + q)).hom c) := by
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
  have ht : triadCapCohomologyLinear ℚ X A B p q
      (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ)) =
      triadRelativeCohomologyCycleCapLinear ℚ X A B p q φ :=
    triadCapCohomologyLinear_on_cycle ℚ X A B p q φ
  apply Eq.trans _ (congrArg (fun f => f
    ((HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) (p + q)).hom c)) ht.symm)
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
      (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyClass τ) c) = _
  have hcap : capCohomologyLinear ℚ X p q
      (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyClass τ) =
      capHomologyMap ℚ X p q (AlgebraicTopology.Simplicial.cohomologyCycleToCocycle ℚ p τ) :=
    AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle ℚ p q τ
  refine (congrArg (fun f : Homology ℚ X (p + q) →ₗ[ℚ] Homology ℚ X q =>
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom (f c)) hcap).trans ?_
  exact properCycle_cap_relative_projection_on_cocycle X A B p q
    (relativeCohomologyCycleToCocycle ℚ P p φ).1
    (relativeCohomologyCycleToCocycle ℚ P p φ).2 c

end HodgeLean.Foundations.QuotientDuality
