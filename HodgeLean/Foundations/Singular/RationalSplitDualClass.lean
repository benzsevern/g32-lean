import HodgeLean.Foundations.Singular.RationalZeroDualClass
import HodgeLean.Foundations.Singular.RationalDualMapNormalization

/-! Functional evaluation after transport to an actual zero-differential rational complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- Transport to a zero-differential rational complex evaluates cocycles through the actual inverse chain map.
Source: Hatcher, Algebraic Topology, §3.1, the universal-coefficient evaluation pairing. -/
theorem rationalSplitDualEquiv_class {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (e : HomotopyEquiv K L) (hL : ∀ i j : ℕ, L.d i j = 0) (n : ℕ)
    (φ : LinearMap.ker (K.sc n).f.hom.dualMap) (z : L.X n) :
    rationalZeroDifferentialDualEquiv L hL n
      ((rationalDualCohomologyHomotopyEquiv e n).symm
        ((K.sc n).linearDual.moduleCatHomologyClass φ)) z = φ.1 ((e.inv.f n).hom z) := by
  let f : (K.sc n).linearDual ⟶ (L.sc n).linearDual :=
    ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map e.inv)
  let ψ := ShortComplex.moduleCatCycleMap f φ
  have hm : rationalDualCohomologyHomotopyEquiv e.symm n
      ((K.sc n).linearDual.moduleCatHomologyClass φ) = (L.sc n).linearDual.moduleCatHomologyClass ψ := by
    change (rationalDualCohomologyHomotopyEquiv e.symm n).toLinearMap _ = _
    rw [rationalDualCohomologyHomotopyEquiv_map]
    exact ShortComplex.moduleCatHomologyClass_naturality f φ
  rw [rationalDualCohomologyHomotopyEquiv_symm, hm]
  exact rationalZeroDifferentialDualEquiv_class L hL n ψ z

#print axioms rationalSplitDualEquiv_class
end HodgeLean.Foundations.Singular
