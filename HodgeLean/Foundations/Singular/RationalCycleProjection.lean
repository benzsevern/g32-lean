import HodgeLean.Foundations.Singular.RationalChainSplitting

/-! Actual cycle projections obtained from rational boundary sections. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Project an actual rational chain onto cycles using a section of its outgoing differential.
Source: Hatcher, Algebraic Topology, §3.2, splitting chain complexes over a field. -/
def rationalCycleProjection (K : ChainComplex (ModuleCat ℚ) ℕ) :
    (n : ℕ) → K.X n →ₗ[ℚ] K.X n
  | 0 => LinearMap.id
  | n + 1 => LinearMap.id -
      (rationalChainBoundarySection K n).comp (K.d (n + 1) n).hom.rangeRestrict

/-- The rational cycle projection takes every actual chain to a cycle.
Source: Hatcher, Algebraic Topology, §3.2, splitting chain complexes over a field. -/
theorem rationalCycleProjection_cycle (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (z : K.X n) :
    (K.d n (n - 1)).hom (rationalCycleProjection K n z) = 0 := by
  cases n with
  | zero =>
    change (K.d 0 0).hom z = 0
    exact congrArg (fun k => ModuleCat.Hom.hom k z) (K.shape 0 0 (by simp))
  | succ n =>
    change (K.d (n + 1) n).hom
      (z - rationalChainBoundarySection K n ((K.d (n + 1) n).hom.rangeRestrict z)) = 0
    rw [map_sub, rationalChainBoundarySection_boundary]
    exact sub_self _

/-- The rational cycle projection fixes every actual cycle.
Source: Hatcher, Algebraic Topology, §3.2, splitting chain complexes over a field. -/
theorem rationalCycleProjection_of_cycle (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X n) (hz : (K.d n (n - 1)).hom z = 0) : rationalCycleProjection K n z = z := by
  cases n with
  | zero => rfl
  | succ n =>
    have hz' : (K.d (n + 1) n).hom.rangeRestrict z = 0 := Subtype.ext hz
    change z - rationalChainBoundarySection K n ((K.d (n + 1) n).hom.rangeRestrict z) = z
    rw [hz', map_zero, sub_zero]

#print axioms rationalCycleProjection_of_cycle
#print axioms rationalCycleProjection
#print axioms rationalCycleProjection_cycle
end HodgeLean.Foundations.Singular
