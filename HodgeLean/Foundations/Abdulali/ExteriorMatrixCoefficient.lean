import HodgeLean.Foundations.Program.MilneExteriorPresentation
import HodgeLean.Foundations.Program.G32Native.PaperExteriorPolynomial
import HodgeLean.Foundations.HodgeGroupAlgebraicGkLie

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}

/-- A coordinate of the exterior action, as a polynomial in matrix entries. -/
def exteriorMatrixCoefficient (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → V)) (i : Set.powersetCard (Fin (d*r)) n) :
    MvPolynomial (Fin d × Fin d) ℂ :=
  ∑ j, MvPolynomial.C (((m2_piBasis b r).exteriorPower n).repr v j) *
    m2_exteriorMatrixPolynomial d r n i j

/-- Evaluation retains the order of the exterior basis indices. -/
theorem eval_exteriorMatrixCoefficient (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → V)) (i : Set.powersetCard (Fin (d*r)) n)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    MvPolynomial.eval (fun ij => U ij.1 ij.2) (exteriorMatrixCoefficient b r n v i) =
      ((m2_piBasis b r).exteriorPower n).repr
        (exteriorPower.map n (m2_diagonalEnd r (Matrix.toLin b b U)) v) i := by
  classical
  simp only [exteriorMatrixCoefficient, map_sum, map_mul, MvPolynomial.eval_C]
  have he := m2_exteriorMatrixPolynomial_eval (K := ℂ) d r n (fun ij => U ij.1 ij.2)
  have hc (j) := congrArg (fun M => M i j) he
  simp only [Matrix.map_apply, MvPolynomial.aeval_eq_eval] at hc
  simp_rw [hc]
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    ((m2_piBasis b r).exteriorPower n) ((m2_piBasis b r).exteriorPower n)
    (exteriorPower.map n (m2_diagonalEnd r (Matrix.toLin b b U))) v) i
  rw [m2_exteriorEnd_matrix, LinearMap.toMatrix_toLin] at h
  exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans h

/-- The differential of an exterior matrix coordinate is the corresponding
coordinate of the exterior derivation. -/
theorem differential_exteriorMatrixCoefficient (b : Module.Basis (Fin d) ℂ V)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V))
    (i : Set.powersetCard (Fin (d*r)) n) (X : Matrix (Fin d) (Fin d) ℂ) :
    g1_differential (exteriorMatrixCoefficient b r n v i) X =
      ((m2_piBasis b r).exteriorPower n).repr
        (InvariantsExterior.exteriorDer n (m2_diagonalEnd r (Matrix.toLin b b X)) v) i := by
  classical
  apply g2k_differential_eq_of_line
  simp_rw [eval_exteriorMatrixCoefficient]
  have hline (t : ℂ) : m2_diagonalEnd r (Matrix.toLin b b (1 + t • X)) =
      1 + t • m2_diagonalEnd r (Matrix.toLin b b X) := by
    rw [map_add, map_smul, Matrix.toLin_one]
    ext w j
    rfl
  simp_rw [hline]
  obtain ⟨p, hp, hp1⟩ := G32Native.paperExterior_exists_polynomial_one_add_smul
    n (m2_diagonalEnd r (Matrix.toLin b b X)) v
    (((m2_piBasis b r).exteriorPower n).coord i)
  have hd := p.hasDerivAt (0 : ℂ)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] at hd
  simp only [Nat.reduceAdd, Nat.cast_zero, zero_add, mul_one] at hd
  simpa only [hp, hp1, Module.Basis.coord_apply] using hd

end HodgeLean.Foundations.Abdulali
