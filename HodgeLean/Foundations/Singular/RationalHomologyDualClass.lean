import HodgeLean.Foundations.Singular.RationalZeroDualClass
import HodgeLean.Foundations.Singular.RationalDualMapNormalization

/-! Evaluation of actual rational dual cohomology on the chosen homology representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The rational homology-dual comparison evaluates a cocycle on the chosen actual homology representative.
Source: Hatcher, Algebraic Topology, §3.1, the universal-coefficient evaluation pairing. -/
theorem rationalHomologyDualEquiv_class (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (φ : LinearMap.ker (K.sc n).f.hom.dualMap) (z : rationalHomologyQuotient K n) :
    rationalHomologyDualEquiv K n ((K.sc n).linearDual.moduleCatHomologyClass φ) z =
      φ.1 (rationalHomologyInclusion K n z) := by
  let e := rationalHomologyHomotopyEquiv K
  let H := rationalHomologyComplex K
  let f : (K.sc n).linearDual ⟶ (H.sc n).linearDual :=
    ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map e.inv)
  let ψ := ShortComplex.moduleCatCycleMap f φ
  have hm : rationalDualCohomologyHomotopyEquiv e.symm n
      ((K.sc n).linearDual.moduleCatHomologyClass φ) = (H.sc n).linearDual.moduleCatHomologyClass ψ := by
    change (rationalDualCohomologyHomotopyEquiv e.symm n).toLinearMap _ = _
    rw [rationalDualCohomologyHomotopyEquiv_map]
    exact ShortComplex.moduleCatHomologyClass_naturality f φ
  change rationalZeroDifferentialDualEquiv H (fun _ _ => rfl) n
    ((rationalDualCohomologyHomotopyEquiv e n).symm
      ((K.sc n).linearDual.moduleCatHomologyClass φ)) z = _
  rw [rationalDualCohomologyHomotopyEquiv_symm, hm]
  exact rationalZeroDifferentialDualEquiv_class H (fun _ _ => rfl) n ψ z

#print axioms rationalHomologyDualEquiv_class
end HodgeLean.Foundations.Singular
