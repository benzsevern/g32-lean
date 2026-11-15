import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing

/-! # The actual relative pullback comparison on cochain homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative pullback agrees with the dual relative chain map under the canonical cochain-homology comparisons.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of cohomology models.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_pullback_cochain_comparison
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p : ℕ) (a : RelativeCochainCohomology ℚ Q p) :
    (relativeCochainCohomologyEquiv ℚ P p).symm
      (relativeCohomologyMap ℚ p f (relativeCochainCohomologyEquiv ℚ Q p a)) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
          ((relativeChainFunctor ℚ).map f)))).hom a := by
  let eA := (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    ((relativeChainFunctor ℚ).obj P) p)).toLinearEquiv
  let eP := (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    ((relativeChainFunctor ℚ).obj Q) p)).toLinearEquiv
  have hn := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality ((relativeChainFunctor ℚ).map f) p)
  rw [Functor.map_comp, Functor.map_comp] at hn
  have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hn) (eP.symm a)
  change eA (relativeCohomologyMap ℚ p f (eP.symm a)) =
    (ShortComplex.homologyMap (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
        ((relativeChainFunctor ℚ).map f)))).hom (eP (eP.symm a)) at hh
  rw [eP.apply_symm_apply] at hh
  exact hh

end HodgeLean.Foundations.QuotientDuality
