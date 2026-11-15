import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing

/-! # The actual relative-to-absolute comparison on cochain homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Forgetting relative support agrees with the actual dual chain projection under the canonical cochain-homology comparisons.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of cohomology models.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_forget_cochain_comparison
    (P : TopPair.{0}) (p : ℕ) (a : RelativeCochainCohomology ℚ P p) :
    (cochainCohomologyEquiv ℚ P.fst p).symm
      (relativeCohomologyToAbsolute ℚ P p (relativeCochainCohomologyEquiv ℚ P p a)) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
          (relativeChainProjection ℚ P)))).hom a := by
  let eA := (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    (SingularChainComplex ℚ P.fst) p)).toLinearEquiv
  let eP := (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    ((relativeChainFunctor ℚ).obj P) p)).toLinearEquiv
  have hn := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality (relativeChainProjection ℚ P) p)
  rw [Functor.map_comp, Functor.map_comp] at hn
  have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hn) (eP.symm a)
  change eA (relativeCohomologyToAbsolute ℚ P p (eP.symm a)) =
    (ShortComplex.homologyMap (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
        (relativeChainProjection ℚ P)))).hom (eP (eP.symm a)) at hh
  rw [eP.apply_symm_apply] at hh
  exact hh

end HodgeLean.Foundations.QuotientDuality
