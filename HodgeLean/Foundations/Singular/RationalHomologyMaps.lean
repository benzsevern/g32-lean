import HodgeLean.Foundations.Singular.RationalHomologySplitting

/-! Actual inclusion and projection maps for rational homology representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Include the chosen representative of an actual homology quotient class into chains.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyInclusion (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    rationalHomologyQuotient K n →ₗ[ℚ] K.X n :=
  (rationalCycles K n).subtype.comp (rationalHomologyRepresentative K n)

/-- Project an actual rational chain to the homology class of its chosen cycle projection.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyProjection (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.X n →ₗ[ℚ] rationalHomologyQuotient K n :=
  (rationalBoundariesInCycles K n).mkQ.comp (rationalCycleRetract K n)

/-- Projection after inclusion of the chosen actual homology representatives is the identity.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalHomologyProjection_inclusion (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (rationalHomologyProjection K n).comp (rationalHomologyInclusion K n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  have he : rationalCycleRetract K n (rationalHomologyRepresentative K n z) =
      rationalHomologyRepresentative K n z :=
    Subtype.ext (rationalCycleProjection_of_cycle K n _ (rationalHomologyRepresentative K n z).property)
  change (rationalBoundariesInCycles K n).mkQ
    (rationalCycleRetract K n (rationalHomologyRepresentative K n z)) = z
  rw [he, rationalHomologyRepresentative_class]

/-- The actual rational homology projection kills every boundary.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalHomologyProjection_boundary (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X (n + 1)) : rationalHomologyProjection K n ((K.d (n + 1) n).hom z) = 0 := by
  have hd : (K.d n (n - 1)).hom ((K.d (n + 1) n).hom z) = 0 :=
    congrArg (fun k => ModuleCat.Hom.hom k z) (K.d_comp_d (n + 1) n (n - 1))
  change (rationalBoundariesInCycles K n).mkQ
    (rationalCycleRetract K n ((K.d (n + 1) n).hom z)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change rationalCycleProjection K n ((K.d (n + 1) n).hom z) ∈
    LinearMap.range (K.d (n + 1) n).hom
  rw [rationalCycleProjection_of_cycle K n _ hd]
  exact ⟨z, rfl⟩

#print axioms rationalHomologyProjection_boundary
#print axioms rationalHomologyInclusion
#print axioms rationalHomologyProjection
#print axioms rationalHomologyProjection_inclusion
end HodgeLean.Foundations.Singular
