import HodgeLean.Foundations.Singular.RationalCycleProjection

/-! Actual cycle quotients and chosen rational representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual rational cycle subspace in a chain degree.
Source: Hatcher, Algebraic Topology, §2.1, cycles of a chain complex. -/
abbrev rationalCycles (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  LinearMap.ker (K.d n (n - 1)).hom

/-- The actual boundary subspace inside the rational cycle space.
Source: Hatcher, Algebraic Topology, §2.1, boundaries and homology. -/
def rationalBoundariesInCycles (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    Submodule ℚ (rationalCycles K n) :=
  (LinearMap.range (K.d (n + 1) n).hom).comap (rationalCycles K n).subtype

/-- The actual quotient of rational cycles by rational boundaries.
Source: Hatcher, Algebraic Topology, §2.1, definition of homology. -/
abbrev rationalHomologyQuotient (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (rationalCycles K n) ⧸ rationalBoundariesInCycles K n

/-- The cycle projection with its codomain restricted to the actual cycle subspace.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalCycleRetract (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.X n →ₗ[ℚ] rationalCycles K n :=
  (rationalCycleProjection K n).codRestrict _ (rationalCycleProjection_cycle K n)

/-- A rational-linear choice of cycle representative for every actual homology quotient class.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyRepresentative (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    rationalHomologyQuotient K n →ₗ[ℚ] rationalCycles K n :=
  Classical.choose ((rationalBoundariesInCycles K n).mkQ.exists_rightInverse_of_surjective
    (rationalBoundariesInCycles K n).range_mkQ)

/-- The chosen rational cycle representative has the specified actual homology class.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalHomologyRepresentative_class (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : rationalHomologyQuotient K n) :
    (rationalBoundariesInCycles K n).mkQ (rationalHomologyRepresentative K n z) = z :=
  LinearMap.congr_fun
    (Classical.choose_spec ((rationalBoundariesInCycles K n).mkQ.exists_rightInverse_of_surjective
      (rationalBoundariesInCycles K n).range_mkQ)) z

#print axioms rationalCycleRetract
#print axioms rationalHomologyRepresentative
#print axioms rationalHomologyRepresentative_class
end HodgeLean.Foundations.Singular
