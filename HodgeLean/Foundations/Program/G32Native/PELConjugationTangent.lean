import HodgeLean.Foundations.MatrixAlgGroupLie

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial
variable {k : Type*} [Field k] {n : ℕ}

/-- Pullback along conjugation by an invertible constant matrix. -/
def pelConjugatePolynomial (g : Matrix.GeneralLinearGroup (Fin n) k) :
    MvPolynomial (Fin n × Fin n) k →ₐ[k] MvPolynomial (Fin n × Fin n) k :=
  bind₁ fun ij =>
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k).map C *
      g1_varMatrix k n * (g : Matrix (Fin n) (Fin n) k).map C :
      Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)) ij.1 ij.2

lemma pel_eval_conjugatePolynomial (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords h) (pelConjugatePolynomial g f) = eval (g1_coords (g⁻¹ * h * g)) f := by
  have hhom : (aeval (g1_coords h)).comp (pelConjugatePolynomial g) =
      aeval (g1_coords (g⁻¹ * h * g)) := by
    ext ij
    simp only [AlgHom.comp_apply, pelConjugatePolynomial, bind₁_X_right]
    have he : (eval (g1_coords h)).mapMatrix
        ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k).map C) *
          g1_varMatrix k n * (g : Matrix (Fin n) (Fin n) k).map C) =
        (g⁻¹ * h * g : Matrix.GeneralLinearGroup (Fin n) k) := by
      have hc (M : Matrix (Fin n) (Fin n) k) :
          (eval (g1_coords h)).mapMatrix (M.map C) = M := by ext i j; simp
      rw [map_mul, map_mul, hc, hc, g1_mapMatrix_eval_varMatrix]
      rfl
    simpa only [aeval_X, g1_coords, RingHom.mapMatrix_apply, Matrix.map_apply, aeval_eq_eval] using
      congrArg (fun M : Matrix (Fin n) (Fin n) k => M ij.1 ij.2) he
  exact congrArg (fun F : MvPolynomial (Fin n × Fin n) k →ₐ[k] k => F f) hhom

lemma pel_differential_conjugate_coordinate (g : Matrix.GeneralLinearGroup (Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) (ij : Fin n × Fin n) :
    g1_differential (pelConjugatePolynomial g (X ij)) Y =
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        Y * (g : Matrix (Fin n) (Fin n) k)) ij.1 ij.2 := by
  simp only [pelConjugatePolynomial, bind₁_X_right, Matrix.mul_apply, Matrix.map_apply,
    g1_varMatrix, Matrix.of_apply]
  simp only [← g1_diffAt_apply, map_sum]
  simp only [g1_diffAt_apply, g1_differential_mul, g1_differential_C,
    g1_differential_X, eval_C, zero_mul, mul_zero, add_zero, zero_add]
  simp only [← g1_diffAt_apply, map_sum]
  simp only [g1_diffAt_apply, g1_differential_C_mul, g1_differential_X]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma pel_differential_conjugatePolynomial (g : Matrix.GeneralLinearGroup (Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) (f : MvPolynomial (Fin n × Fin n) k) :
    g1_differential (pelConjugatePolynomial g f) Y =
      g1_differential f
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          Y * (g : Matrix (Fin n) (Fin n) k)) := by
  let L := (g1_diffAt Y).comp (pelConjugatePolynomial g).toLinearMap
  have hL (p : MvPolynomial (Fin n × Fin n) k) :
      L p = g1_differential (pelConjugatePolynomial g p) Y := rfl
  have h1 (p : MvPolynomial (Fin n × Fin n) k) :
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pelConjugatePolynomial g p) =
        eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) p := by
    rw [pel_eval_conjugatePolynomial]
    simp only [mul_one, inv_mul_cancel]
  rw [← hL, g1_pointDeriv_eq (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) L (fun p q => by
    simp only [hL, map_mul, g1_differential_mul, h1]), g1_differential_apply_dir]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hL, pel_differential_conjugate_coordinate]

/-- A group normalizer acts on the tangent space by conjugation. -/
theorem pel_conjugate_mem_tangent (H : MatrixAlgGroup k n)
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (hg : ∀ h ∈ H.carrier, g⁻¹ * h * g ∈ H.carrier)
    (Y : Matrix (Fin n) (Fin n) k) (hY : Y ∈ g1_lieAlgebra H) :
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
      Y * (g : Matrix (Fin n) (Fin n) k)) ∈ g1_lieAlgebra H := by
  rw [g1_lieAlgebra, g1_mem_lieOfSet_iff] at hY ⊢
  intro f hf
  rw [← pel_differential_conjugatePolynomial]
  apply hY
  apply g1_mem_vanishingIdealSet_iff.mpr
  intro h hh
  rw [pel_eval_conjugatePolynomial]
  exact g1_mem_vanishingIdealSet_iff.mp hf _ (hg h hh)

end HodgeLean.Foundations.Program.GeneralTypeIII
