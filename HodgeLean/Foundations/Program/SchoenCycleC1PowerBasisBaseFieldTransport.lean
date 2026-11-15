import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.Field

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A compatible base-field identification transports the power basis
without changing its covering-field generator or dimension, and maps its
exact minimal polynomial coefficientwise. -/
theorem s2e_c1_power_basis_base_field_transport
    {K₀ K₁ L : Type*} [Field K₀] [Field K₁] [Field L]
    [Algebra K₀ L] [Algebra K₁ L]
    (E : K₀ ≃+* K₁)
    (hE : ∀ k, algebraMap K₁ L (E k) = algebraMap K₀ L k)
    (P : PowerBasis K₀ L) :
    ∃ Q : PowerBasis K₁ L, Q.gen = P.gen ∧ Q.dim = P.dim ∧
      minpoly K₁ Q.gen = (minpoly K₀ P.gen).map E.toRingHom := by
  have hs (k : K₀) (x : L) : E k • x = k • x := by
    simp only [Algebra.smul_def, hE]
  let Q : PowerBasis K₁ L := {
    dim := P.dim
    gen := P.gen
    basis := P.basis.mapCoeffs E hs
    basis_eq_pow := fun i => by rw [Module.Basis.mapCoeffs_apply, P.basis_eq_pow] }
  letI : Module.Finite K₀ L := P.finite
  have hcomp : (algebraMap K₁ L).comp E.toRingHom =
      (RingHom.id L).comp (algebraMap K₀ L) := RingHom.ext hE
  refine ⟨Q, rfl, rfl, ?_⟩
  exact (minpoly.map_eq_of_equiv_equiv (f := E) (g := RingEquiv.refl L) hcomp P.gen).symm

end HodgeLean.Foundations.Program
