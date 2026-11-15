import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapCocycleNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativePullbackCochain

/-! # Naturality of the original relative cap product on cohomology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative cap pairing is natural on the repository's actual cohomology and homology objects for every map of pairs.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (a : RelativeCohomology ℚ Q p) (c : RelativeHomology ℚ P (p + q)) :
    homologyMap ℚ q (TopPair.Hom.fst f)
      (relativeCapCohomologyLinear ℚ P p q (relativeCohomologyMap ℚ p f a) c) =
      relativeCapCohomologyLinear ℚ Q p q a (relativeHomologyMap ℚ (p + q) f c) := by
  let SQ := ((relativeChainFunctor ℚ).obj Q).sc p
  let SP := ((relativeChainFunctor ℚ).obj P).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ Q p).surjective a
  obtain ⟨φ, rfl⟩ := SQ.linearDual.moduleCatHomologyClass_surjective u
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
    ((relativeChainFunctor ℚ).map f)
  let τ := ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) φ
  have hα : relativeCohomologyMap ℚ p f
      (relativeCochainCohomologyEquiv ℚ Q p (SQ.linearDual.moduleCatHomologyClass φ)) =
      relativeCochainCohomologyEquiv ℚ P p (SP.linearDual.moduleCatHomologyClass τ) := by
    have h := congrArg (relativeCochainCohomologyEquiv ℚ P p)
      (properCycle_relative_pullback_cochain_comparison f p (SQ.linearDual.moduleCatHomologyClass φ))
    rw [LinearEquiv.apply_symm_apply, ShortComplex.moduleCatHomologyClass_naturality] at h
    exact h
  refine (congrArg (fun z : RelativeCohomology ℚ P p =>
    homologyMap ℚ q (TopPair.Hom.fst f) (relativeCapCohomologyLinear ℚ P p q z c)) hα).trans ?_
  have hp : relativeCapCohomologyLinear ℚ P p q
      (relativeCochainCohomologyEquiv ℚ P p (SP.linearDual.moduleCatHomologyClass τ)) =
      relativeCohomologyCycleCapLinear ℚ P p q τ := relativeCapCohomologyLinear_on_cycle ℚ P p q τ
  have hq : relativeCapCohomologyLinear ℚ Q p q
      (relativeCochainCohomologyEquiv ℚ Q p (SQ.linearDual.moduleCatHomologyClass φ)) =
      relativeCohomologyCycleCapLinear ℚ Q p q φ := relativeCapCohomologyLinear_on_cycle ℚ Q p q φ
  refine (congrArg (homologyMap ℚ q (TopPair.Hom.fst f)) (LinearMap.congr_fun hp c)).trans ?_
  refine Eq.trans ?_ (LinearMap.congr_fun hq (relativeHomologyMap ℚ (p + q) f c)).symm
  exact properCycle_relative_cap_cocycle_naturality f p q
    (relativeCohomologyCycleToCocycle ℚ Q p φ).1
    (relativeCohomologyCycleToCocycle ℚ Q p φ).2 c

end HodgeLean.Foundations.QuotientDuality
