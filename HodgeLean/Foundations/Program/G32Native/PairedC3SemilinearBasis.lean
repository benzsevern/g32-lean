import Mathlib.LinearAlgebra.Basis.Basic

/-! # Transporting specified bases with their quotient coefficient rings -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- Pull a specified basis back through a semilinear equivalence, retaining
its indices while changing coefficients by the original ring equivalence. -/
def pairedC3SemilinearBasis {R S M N ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (q : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv q
    haveI := RingHomInvPair.of_ringEquiv_symm q
    (M ≃ₛₗ[(q : R →+* S)] N) → Module.Basis ι S N → Module.Basis ι R M := by
  letI := RingHomInvPair.of_ringEquiv q
  letI := RingHomInvPair.of_ringEquiv_symm q
  letI := RingHomInvPair.of_ringEquiv q.symm
  letI := RingHomInvPair.of_ringEquiv_symm q.symm
  intro e b
  exact Module.Basis.ofRepr ((e.trans b.repr).trans
    (Finsupp.mapRange.linearEquiv q.symm.toSemilinearEquiv))


/-- The transported basis keeps the inverse images of the specified original generators. -/
theorem paired_c3_semilinear_basis_apply
    {R S M N ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] (q : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv q
    haveI := RingHomInvPair.of_ringEquiv_symm q
    ∀ (e : M ≃ₛₗ[(q : R →+* S)] N) (b : Module.Basis ι S N) (i : ι),
      pairedC3SemilinearBasis q e b i = e.symm (b i) := by
  letI := RingHomInvPair.of_ringEquiv q
  letI := RingHomInvPair.of_ringEquiv_symm q
  intro e b i
  change e.symm (b.repr.symm (Finsupp.mapRange q q.map_zero (Finsupp.single i 1))) = _
  simp

#print axioms paired_c3_semilinear_basis_apply
#print axioms pairedC3SemilinearBasis
end HodgeLean.Foundations.Program.G32Native
