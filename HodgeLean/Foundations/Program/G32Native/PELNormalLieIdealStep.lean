import HodgeLean.Foundations.Program.G32Native.PELFullLieContainment
import HodgeLean.Foundations.Program.G32Native.PELConjugationTangent
import HodgeLean.Foundations.Program.G32Native.PELPolynomialMatrixDifferential

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial
set_option maxHeartbeats 400000

/-- Normalization of a matrix algebraic subgroup differentiates to stability
of its tangent space under the ambient Lie bracket.
Source: Borel, Linear Algebraic Groups, second edition, §§3.4–3.5, 7.1;
Humphreys, Linear Algebraic Groups, §§9.1–9.2, 13.1. -/
theorem pel_normal_subgroup_lie_ideal_aux
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (G H : MatrixAlgGroup k n)
    (hnormal : ∀ g ∈ G.carrier, ∀ h ∈ H.carrier, g⁻¹ * h * g ∈ H.carrier)
    (X Y : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ g1_lieAlgebra G) (hY : Y ∈ g1_lieAlgebra H) :
    X * Y - Y * X ∈ g1_lieAlgebra H := by
  let A := (g1_varMatrix k n).adjugate * Y.map C * g1_varMatrix k n
  have hA (g : Matrix.GeneralLinearGroup (Fin n) k) :
      (eval (g1_coords g)).mapMatrix A = (g : Matrix (Fin n) (Fin n) k).det •
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          Y * (g : Matrix (Fin n) (Fin n) k)) := by
    have hc : (eval (g1_coords g)).mapMatrix (Y.map C) = Y := by ext i j; simp
    dsimp only [A]
    rw [map_mul, map_mul, RingHom.map_adjugate, g1_mapMatrix_eval_varMatrix, hc]
    have hi : (g : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 :=
      congrArg Units.val (mul_inv_cancel g)
    have hadj : (g : Matrix (Fin n) (Fin n) k).adjugate =
        (g : Matrix (Fin n) (Fin n) k).det •
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      calc
        _ = (g : Matrix (Fin n) (Fin n) k).adjugate *
            ((g : Matrix (Fin n) (Fin n) k) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
                rw [hi, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, smul_mul_assoc, Matrix.one_mul]
    rw [hadj, smul_mul_assoc, smul_mul_assoc]
  have hXt := g1_mem_lieOfSet_iff.mp hX
  have hYt := g1_mem_lieOfSet_iff.mp hY
  apply g1_mem_lieOfSet_iff.mpr
  intro f hf
  have hQ : pelTangentPolynomial f A ∈ g1_vanishingIdealSet (G.carrier : Set _) := by
    apply g1_mem_vanishingIdealSet_iff.mpr
    intro g hg
    rw [pel_eval_tangentPolynomial, hA, map_smul]
    have hc := pel_conjugate_mem_tangent H g (hnormal g hg) Y hY
    have hct := g1_mem_lieOfSet_iff.mp hc
    rw [hct f hf, smul_zero]
  have hd := hXt _ hQ
  rw [pel_differential_tangentPolynomial] at hd
  change g1_differential f (pelMatrixDifferential X
    ((g1_varMatrix k n).adjugate * Y.map C * g1_varMatrix k n)) = 0 at hd
  rw [pelMatrixDifferential_adjugate_conjugation, map_sub, map_smul, hYt f hf,
    smul_zero, zero_sub] at hd
  exact neg_eq_zero.mp hd

end HodgeLean.Foundations.Program.GeneralTypeIII
