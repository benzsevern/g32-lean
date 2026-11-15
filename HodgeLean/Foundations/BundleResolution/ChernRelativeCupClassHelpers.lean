import HodgeLean.Foundations.BundleResolution.ChernRelativeCocycleClassHelpers

/-! # Relative cap action on explicit cocycle classes

The relative cup pairing can be calculated using actual relative cycles
and the cap morphism of the singular short complexes.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCapCohomologyLinear_class (φ : RelativeCocycle ℚ P p) :
    relativeCapCohomologyLinear ℚ P p q (i1_relativeCocycleClass P p φ) =
      relativeCapHomologyMap ℚ P p q φ.val φ.property := by
  change relativeCapCohomologyLinear ℚ P p q
    (relativeCochainCohomologyEquiv ℚ P p
      (((((relativeChainFunctor ℚ).obj P).sc p).linearDual).moduleCatHomologyIso.inv.hom
        (Submodule.Quotient.mk (i1_relativeCocycleToDualCycle P p φ)))) = _
  rw [relativeCapCohomologyLinear_on_cycle]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCup_pairing_cycle (φ : RelativeCocycle ℚ P p)
    (β : Cohomology ℚ P.fst q)
    (z : LinearMap.ker (((relativeChainFunctor ℚ).obj P).sc (p + q)).g.hom) :
    relativeCohomologyEquivDualHomology ℚ P (p + q)
      (i1_relativeCup P p q (i1_relativeCocycleClass P p φ) β)
      ((((relativeChainFunctor ℚ).obj P).sc (p + q)).moduleCatHomologyClass z) =
    cohomologyEquivDualHomology ℚ P.fst q β
      (((SingularChainComplex ℚ P.fst).sc q).moduleCatHomologyClass
        (ShortComplex.moduleCatCycleMap
          (relativeCapShortComplexHom ℚ P p q φ.val φ.property) z)) := by
  rw [i1_relativeCup_pairing, i1_relativeCapCohomologyLinear_class]
  change cohomologyEquivDualHomology ℚ P.fst q β
    ((ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P p q φ.val φ.property)).hom
      ((((relativeChainFunctor ℚ).obj P).sc (p + q)).moduleCatHomologyClass z)) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]

end HodgeLean.Foundations.BundleResolution
