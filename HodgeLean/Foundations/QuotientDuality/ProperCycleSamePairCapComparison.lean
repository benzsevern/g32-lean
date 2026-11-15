import HodgeLean.Foundations.QuotientDuality.ProperCycleSamePairCapProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeForgetCochain

/-! # Original same-pair cap comparison without representatives -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original absolute cap image equals the same-pair relative cap of the original projected homology class.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative cap products and excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_same_pair_cap_projection_cohomology
    (P : TopPair.{0}) (p q : ℕ)
    (a : RelativeCohomology ℚ P p)
    (c : Homology ℚ P.fst (p + q)) :
    capCohomologyLinear ℚ P.fst p q
        ((cochainCohomologyEquiv ℚ P.fst p).symm
          (relativeCohomologyToAbsolute ℚ P p a)) c =
      relativeCapCohomologyLinear ℚ P p q a
        ((relativeHomologyProjection ℚ P (p + q)).hom c) := by
  let S := ((relativeChainFunctor ℚ).obj P).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ P p).surjective a
  obtain ⟨φ, rfl⟩ := S.linearDual.moduleCatHomologyClass_surjective u
  have hpull : (cochainCohomologyEquiv ℚ P.fst p).symm
      (relativeCohomologyToAbsolute ℚ P p
        (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ))) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
          (relativeChainProjection ℚ P)))).hom (S.linearDual.moduleCatHomologyClass φ) :=
    properCycle_relative_forget_cochain_comparison P p _
  have ht : relativeCapCohomologyLinear ℚ P p q
      (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ)) =
      relativeCohomologyCycleCapLinear ℚ P p q φ :=
    relativeCapCohomologyLinear_on_cycle ℚ P p q φ
  apply Eq.trans _ (congrArg (fun f => f
    ((relativeHomologyProjection ℚ P (p + q)).hom c)) ht.symm)
  refine (congrArg (fun z : CochainCohomology ℚ P.fst p =>
    capCohomologyLinear ℚ P.fst p q z c) hpull).trans ?_
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
    (relativeChainProjection ℚ P)
  let τ : LinearMap.ker (((SingularChainComplex ℚ P.fst).sc p).linearDual.g.hom) :=
    ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) φ
  change capCohomologyLinear ℚ P.fst p q
      (((SingularChainComplex ℚ P.fst).sc p).linearDual.moduleCatHomologyClass τ) c = _
  have hcap : capCohomologyLinear ℚ P.fst p q
      (((SingularChainComplex ℚ P.fst).sc p).linearDual.moduleCatHomologyClass τ) =
      capHomologyMap ℚ P.fst p q (AlgebraicTopology.Simplicial.cohomologyCycleToCocycle ℚ p τ) :=
    AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle ℚ p q τ
  refine (congrArg (fun f : Homology ℚ P.fst (p + q) →ₗ[ℚ] Homology ℚ P.fst q =>
    f c) hcap).trans ?_
  exact properCycle_same_pair_cap_projection_on_cocycle P p q
    (relativeCohomologyCycleToCocycle ℚ P p φ).1
    (relativeCohomologyCycleToCocycle ℚ P p φ).2 c

end HodgeLean.Foundations.QuotientDuality
