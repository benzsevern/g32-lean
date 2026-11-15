import HodgeLean.Foundations.Program.SchoenTowerL1aRationalKernels
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Pointwise

/-! # Rational point stabilizers in section rings

Implication from rational evaluation kernels to equality of the actual
translated evaluation maps. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- A group element stabilizes a rational evaluation kernel exactly when the
translated evaluation is the original evaluation, with the inverse convention.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and residue fields. -/
theorem s2v_l1a_rational_kernel_stabilizer
    {K A G : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [Group G] [MulSemiringAction G A] [SMulCommClass G K A]
    (φ : A →ₐ[K] K) (g : G) :
    g • RingHom.ker φ.toRingHom = RingHom.ker φ.toRingHom ↔
      φ.comp (MulSemiringAction.toAlgHom K A g⁻¹) = φ := by
  let ψ := φ.comp (MulSemiringAction.toAlgHom K A g⁻¹)
  have hker : g • RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := by
    ext a
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [hker]
  constructor
  · intro h
    apply AlgHom.coe_ringHom_injective
    apply s2v_l1a_rational_evaluations_eq_of_kernel_eq (algebraMap K A)
      ψ.toRingHom φ.toRingHom
    · ext c
      exact ψ.commutes c
    · ext c
      exact φ.commutes c
    · exact h
  · intro h
    exact congrArg (fun f : A →ₐ[K] K => RingHom.ker f.toRingHom) h

end HodgeLean.Foundations.Program
