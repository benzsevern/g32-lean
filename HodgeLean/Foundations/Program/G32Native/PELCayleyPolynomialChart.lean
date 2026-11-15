import HodgeLean.Foundations.Program.G32Native.PELRealRationalDetermination
import HodgeLean.Foundations.Program.G32Native.PELBilinearCayley

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations
open MvPolynomial MatrixCayley
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The Cayley chart has polynomial numerators and the determinant of
`1 + X` as its common denominator. -/
theorem pel_cayley_polynomial_numerators
    (X : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ)) (z : ι → ℂ)
    (hz : eval z (1 + X).det ≠ 0) (i j : Fin n) :
    eval z (((1 - X) * (1 + X).adjugate) i j) =
      eval z (1 + X).det * (cayley ((eval z).mapMatrix X)) i j := by
  let M := (eval z).mapMatrix X
  have hdet : (1 + M).det ≠ 0 := by
    simpa only [RingHom.map_det, map_add, map_one] using hz
  have ha : (1 + M).adjugate = (1 + M).det • (1 + M)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul,
      mul_inv_cancel₀ hdet, one_smul]
  have hm : (eval z).mapMatrix ((1 - X) * (1 + X).adjugate) =
      (1 + M).det • cayley M := by
    rw [map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one]
    change (1 - M) * (1 + M).adjugate = _
    rw [ha, Matrix.mul_smul]
    rfl
  have hd : eval z (1 + X).det = (1 + M).det := by
    rw [RingHom.map_det, map_add, map_one]
  rw [hd]
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) hm

/-- An equation in Cayley coordinates that holds for all real parameters
near a point holds at every complex parameter in the determinant chart. -/
theorem pel_cayley_equation_of_real_nhds
    (X : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ))
    (p : MvPolynomial (Fin n × Fin n) ℂ) (a : ι → ℝ)
    (hdet : ∀ᶠ t in nhds a, eval (fun i => (t i : ℂ)) (1 + X).det ≠ 0)
    (hp : ∀ᶠ t in nhds a,
      eval (fun ij : Fin n × Fin n => cayley ((eval (fun i => (t i : ℂ))).mapMatrix X) ij.1 ij.2) p = 0) :
    ∀ z, eval z (1 + X).det ≠ 0 →
      eval (fun ij : Fin n × Fin n => cayley ((eval z).mapMatrix X) ij.1 ij.2) p = 0 := by
  exact pel_rational_equation_of_real_nhds (1 + X).det
    (fun ij : Fin n × Fin n => ((1 - X) * (1 + X).adjugate) ij.1 ij.2)
    (fun (z : ι → ℂ) (ij : Fin n × Fin n) => cayley ((eval z).mapMatrix X) ij.1 ij.2)
    (fun z hz ij => pel_cayley_polynomial_numerators X z hz ij.1 ij.2) p a hdet hp

end HodgeLean.Foundations
