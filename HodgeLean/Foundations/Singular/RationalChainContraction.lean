import HodgeLean.Foundations.Singular.RationalHomologyMaps

/-! Contraction of the boundary summands of an actual rational chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Removing the chosen homology representative from the cycle projection gives an actual boundary.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalRepresentativeResidual_mem_range (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X n) :
    rationalCycleProjection K n z - rationalHomologyInclusion K n (rationalHomologyProjection K n z) ∈
      LinearMap.range (K.d (n + 1) n).hom := by
  have h : rationalCycleRetract K n z -
      rationalHomologyRepresentative K n (rationalHomologyProjection K n z) ∈
      rationalBoundariesInCycles K n := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (rationalBoundariesInCycles K n).mkQ
      (rationalCycleRetract K n z -
        rationalHomologyRepresentative K n (rationalHomologyProjection K n z)) = 0
    rw [map_sub, rationalHomologyRepresentative_class]
    exact sub_self _
  exact h

/-- The actual boundary part of a rational chain after removing its homology representative.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalBoundaryProjection (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.X n →ₗ[ℚ] LinearMap.range (K.d (n + 1) n).hom :=
  (rationalCycleProjection K n - (rationalHomologyInclusion K n).comp
    (rationalHomologyProjection K n)).codRestrict _ (rationalRepresentativeResidual_mem_range K n)

/-- The actual degree-raising rational chain contraction of the chosen boundary part.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalChainContraction (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.X n →ₗ[ℚ] K.X (n + 1) :=
  (rationalChainBoundarySection K n).comp (rationalBoundaryProjection K n)

/-- The boundary of the actual contraction is the cycle projection minus its homology representative.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalChainContraction_boundary (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X n) :
    (K.d (n + 1) n).hom (rationalChainContraction K n z) =
      rationalCycleProjection K n z - rationalHomologyInclusion K n (rationalHomologyProjection K n z) :=
  rationalChainBoundarySection_boundary K n (rationalBoundaryProjection K n z)

/-- On an actual boundary the contraction is exactly its chosen linear primitive.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalChainContraction_of_boundary (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X (n + 1)) :
    rationalChainContraction K n ((K.d (n + 1) n).hom z) =
      rationalChainBoundarySection K n ((K.d (n + 1) n).hom.rangeRestrict z) := by
  change rationalChainBoundarySection K n
    (rationalBoundaryProjection K n ((K.d (n + 1) n).hom z)) = _
  apply congrArg (rationalChainBoundarySection K n)
  apply Subtype.ext
  change rationalCycleProjection K n ((K.d (n + 1) n).hom z) -
    rationalHomologyInclusion K n (rationalHomologyProjection K n ((K.d (n + 1) n).hom z)) =
      (K.d (n + 1) n).hom z
  rw [rationalHomologyProjection_boundary, map_zero, sub_zero]
  apply rationalCycleProjection_of_cycle
  exact congrArg (fun k => ModuleCat.Hom.hom k z) (K.d_comp_d (n + 1) n (n - 1))

/-- The actual contraction and chosen homology representative recover every degree-zero rational chain.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalChainContraction_identity_zero (K : ChainComplex (ModuleCat ℚ) ℕ)
    (z : K.X 0) :
    (K.d 1 0).hom (rationalChainContraction K 0 z) +
      rationalHomologyInclusion K 0 (rationalHomologyProjection K 0 z) = z := by
  rw [rationalChainContraction_boundary]
  change (z - rationalHomologyInclusion K 0 (rationalHomologyProjection K 0 z)) +
    rationalHomologyInclusion K 0 (rationalHomologyProjection K 0 z) = z
  exact sub_add_cancel _ _

#print axioms rationalChainContraction_identity_zero
#print axioms rationalChainContraction_of_boundary
#print axioms rationalChainContraction_boundary
#print axioms rationalRepresentativeResidual_mem_range
#print axioms rationalBoundaryProjection
#print axioms rationalChainContraction
end HodgeLean.Foundations.Singular
