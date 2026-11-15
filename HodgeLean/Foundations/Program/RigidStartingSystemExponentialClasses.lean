import HodgeLean.Foundations.Program.RigidStartingSystemEigenCertificates
import HodgeLean.Foundations.Program.RigidStartingSystemGeneratorEigenbasis
import HodgeLean.Foundations.Program.RigidStartingSystemExponentials
import HodgeLean.Foundations.Program.RigidStartingSystemScalarExp

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def b65r_sourceUnit (i : Fin 4) : (Matrix (Fin 4) (Fin 4) ℂ)ˣ where
  val := b65r_sourceBasis i
  inv := b65r_sourceInverse i
  val_inv := b65r_source_basis_inverse i
  inv_val := mul_eq_one_comm.mp (b65r_source_basis_inverse i)

def b65r_targetUnit (i : Fin 4) : (Matrix (Fin 4) (Fin 4) ℂ)ˣ where
  val := b65r_targetBasis g32h_omega i
  inv := b65r_targetInverse g32h_omega i
  val_inv := b65r_target_basis_inverse g32h_omega g32h_omega_sq_add i
  inv_val := mul_eq_one_comm.mp (b65r_target_basis_inverse g32h_omega g32h_omega_sq_add i)

theorem b65r_printed_matrix (i : Fin 4) :
    b4b_toMatrix (b4b_generators i) =
      ![g32R1 g32h_omega, g32R2 g32h_omega, g32X g32h_omega, g32Y g32h_omega] i := by
  fin_cases i <;> rfl

theorem b65r_residue_exponential_class (i : Fin 4) :
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
        NormedSpace.exp ((2*Real.pi*Complex.I) • b65r_operator (b65r_residues i)) *
        ↑(C⁻¹) = b65r_operator (b4b_toMatrix (b4b_generators i)) := by
  let P := Units.map (b65r_operatorEquiv 4).toAlgHom.toMonoidHom (b65r_sourceUnit i)
  let Q := Units.map (b65r_operatorEquiv 4).toAlgHom.toMonoidHom (b65r_targetUnit i)
  apply b65r_conjugate_of_eigenbases _ _ P Q
    (b65r_eigenvalues i) (b65r_localEigenvalues g32h_omega i) (2*Real.pi*Complex.I)
  · change b65r_operator (b65r_residues i)*b65r_operator (b65r_sourceBasis i) =
      b65r_operator (b65r_sourceBasis i)*b65r_operator (diagonal (b65r_eigenvalues i))
    rw [← b65r_operator_mul, ← b65r_operator_mul, b65r_source_eigenbasis]
  · change b65r_operator (b4b_toMatrix (b4b_generators i))*
      b65r_operator (b65r_targetBasis g32h_omega i) =
        b65r_operator (b65r_targetBasis g32h_omega i)*
          b65r_operator (diagonal (b65r_localEigenvalues g32h_omega i))
    rw [← b65r_operator_mul, ← b65r_operator_mul, b65r_printed_matrix,
      b65r_target_eigenbasis g32h_omega g32h_omega_sq_add]
  · exact b65r_scalar_exponential i

end HodgeLean.Foundations.Program
