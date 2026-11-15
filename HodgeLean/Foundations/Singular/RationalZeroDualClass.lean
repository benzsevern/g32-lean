import HodgeLean.Foundations.Singular.RationalZeroClass
import HodgeLean.Foundations.Singular.RationalDualComparison

/-! Evaluation normalization of actual zero-differential rational dual cohomology. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- Dual cohomology of a zero-differential complex evaluates the represented functional on each actual vector.
Source: Hatcher, Algebraic Topology, §3.1, the universal-coefficient evaluation pairing. -/
theorem rationalZeroDifferentialDualEquiv_class (K : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ i j : ℕ, K.d i j = 0) (n : ℕ)
    (φ : LinearMap.ker (K.sc n).f.hom.dualMap) (z : K.X n) :
    rationalZeroDifferentialDualEquiv K hK n ((K.sc n).linearDual.moduleCatHomologyClass φ) z = φ.1 z := by
  let S := K.sc n
  have hf : S.f = 0 := hK _ _
  have hg : S.g = 0 := hK _ _
  let u : LinearMap.ker S.g.hom := ⟨z, by change S.g.hom z = 0; rw [hg]; rfl⟩
  let e := rationalZeroDifferentialHomologyIso K hK n
  have he : e.hom.hom (S.moduleCatHomologyClass u) = z :=
    rationalZeroShortHomology_class S hf hg u
  have hu : e.inv.hom z = S.moduleCatHomologyClass u :=
    (LinearEquiv.symm_apply_eq e.toLinearEquiv).mpr he.symm
  change S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass φ) (e.inv.hom z) = φ.1 z
  rw [hu]
  exact S.linearDualHomologyEquiv_class_apply_class φ u

#print axioms rationalZeroDifferentialDualEquiv_class
end HodgeLean.Foundations.Singular
