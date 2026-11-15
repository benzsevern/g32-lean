import HodgeLean.Foundations.BundleResolution.ChernDualCycleClassHelpers
import HodgeLean.Foundations.Singular.Cup

/-! # Evaluation of actual singular cocycle classes

The existing singular class map and the dual short-complex representative
give the same evaluation on each singular homology cycle.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (X : TopCat) (n : ℕ)

def i1_cocycleToDualCycle :
    Cocycle ℚ (TopCat.toSSet.obj X) n →ₗ[ℚ]
      LinearMap.ker ((SingularChainComplex ℚ X).sc n).f.hom.dualMap where
  toFun φ := ⟨φ.val, by
    change ((SingularChainComplex ℚ X).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.val = 0
    rw [ChainComplex.prev]
    exact φ.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem i1_cohomologyClass_pairing
    (φ : Cocycle ℚ (TopCat.toSSet.obj X) n)
    (z : LinearMap.ker ((SingularChainComplex ℚ X).sc n).g.hom) :
    cohomologyEquivDualHomology ℚ X n (cohomologyClass X n φ)
      (((SingularChainComplex ℚ X).sc n).moduleCatHomologyClass z) = φ.val z.val := by
  exact i1_chainDualCycleClass_pairing (SingularChainComplex ℚ X) n
    (i1_cocycleToDualCycle X n φ) z

end HodgeLean.Foundations.BundleResolution
