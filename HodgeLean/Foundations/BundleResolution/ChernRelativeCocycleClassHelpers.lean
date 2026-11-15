import HodgeLean.Foundations.BundleResolution.ChernDualCycleClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupHelpers

/-! # Relative cocycle representatives for the actual cohomology group

The dual short-complex comparison sends actual relative cocycles to their
cohomology classes and evaluates them on relative cycle representatives.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (n : ℕ)

def i1_relativeCocycleToDualCycle :
    RelativeCocycle ℚ P n →ₗ[ℚ]
      LinearMap.ker ((((relativeChainFunctor ℚ).obj P).sc n).f.hom.dualMap) where
  toFun φ := ⟨φ.val, by
    change (((relativeChainFunctor ℚ).obj P).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.val = 0
    rw [ChainComplex.prev]
    exact φ.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def i1_relativeCocycleClass :
    RelativeCocycle ℚ P n →ₗ[ℚ] RelativeCohomology ℚ P n :=
  (i1_chainDualCycleClass ((relativeChainFunctor ℚ).obj P) n).comp
    (i1_relativeCocycleToDualCycle P n)

theorem i1_relativeCocycleClass_surjective : Function.Surjective (i1_relativeCocycleClass P n) := by
  intro α
  obtain ⟨φ, hφ⟩ := i1_chainDualCycleClass_surjective ((relativeChainFunctor ℚ).obj P) n α
  refine ⟨relativeCohomologyCycleToCocycle ℚ P n φ, ?_⟩
  exact hφ

theorem i1_relativeCocycleClass_pairing (φ : RelativeCocycle ℚ P n)
    (z : LinearMap.ker (((relativeChainFunctor ℚ).obj P).sc n).g.hom) :
    relativeCohomologyEquivDualHomology ℚ P n (i1_relativeCocycleClass P n φ)
      ((((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass z) = φ.val z.val :=
  i1_chainDualCycleClass_pairing ((relativeChainFunctor ℚ).obj P) n
    (i1_relativeCocycleToDualCycle P n φ) z

end HodgeLean.Foundations.BundleResolution
