import HodgeLean.Foundations.Program.MilneTensorPairing
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem m1b_multilinear_coordinate_expansion
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (v : Fin n → ι → ℂ) :
    f v = ∑ a : Fin n → ι, (∏ i, v i (a i)) * f (fun i => Pi.single (a i) 1) := by
  classical
  have hv (i : Fin n) : v i = ∑ j, v i j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply, apply_ite]
  calc
    f v = f (fun i => ∑ j, v i j • Pi.single j (1 : ℂ)) := congrArg f (funext hv)
    _ = ∑ a : Fin n → ι, f (fun i => v i (a i) • Pi.single (a i) (1 : ℂ)) :=
      f.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [f.map_smul_univ]
      rfl

def m1b_multilinearPolynomial
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) : MvPolynomial (Fin n × ι) ℂ :=
  ∑ a : Fin n → ι, MvPolynomial.C (f (fun i => Pi.single (a i) 1)) *
    ∏ i, MvPolynomial.X (i, a i)

theorem m1b_multilinearPolynomial_eval
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (fun p : Fin n × ι => v p.1 p.2) (m1b_multilinearPolynomial f) = f v := by
  rw [m1b_multilinear_coordinate_expansion f v]
  simp only [m1b_multilinearPolynomial, map_sum, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem m1b_multilinear_adjugate_denominator
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (M : Matrix ι ι ℂ) (hM : IsUnit M) (v : Fin n → ι → ℂ) :
    f (fun i => M.adjugate *ᵥ v i) = M.det ^ n * f (fun i => M⁻¹ *ᵥ v i) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hv (i : Fin n) : M.adjugate *ᵥ v i = M.det • (M⁻¹ *ᵥ v i) := by
    rw [← Matrix.cramer_eq_adjugate_mulVec]
    exact (M.det_smul_inv_mulVec_eq_cramer (v i) hdet).symm
  calc
    f (fun i => M.adjugate *ᵥ v i) = f (fun i => M.det • (M⁻¹ *ᵥ v i)) :=
      congrArg f (funext hv)
    _ = _ := by
      rw [f.map_smul_univ]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def m1b_matrixVariables (n : ℕ) :
    Matrix ι ι (MvPolynomial ((ι × ι) ⊕ (Fin n × ι)) ℂ) :=
  fun i j => MvPolynomial.X (Sum.inl (i, j))

theorem m1b_adjugateVariables_eval (M : Matrix ι ι ℂ) (v : Fin n → ι → ℂ) (i j : ι) :
    MvPolynomial.eval (Sum.elim (fun p : ι × ι => M p.1 p.2)
      (fun p : Fin n × ι => v p.1 p.2)) ((m1b_matrixVariables (ι := ι) n).adjugate i j) =
      M.adjugate i j := by
  let ev := MvPolynomial.eval (Sum.elim (fun p : ι × ι => M p.1 p.2)
    (fun p : Fin n × ι => v p.1 p.2))
  have hX : ev.mapMatrix (m1b_matrixVariables (ι := ι) n) = M := by
    ext a b
    change ev (m1b_matrixVariables n a b) = M a b
    simp only [ev, m1b_matrixVariables, MvPolynomial.eval_X, Sum.elim_inl]
  have h := ev.map_adjugate (m1b_matrixVariables (ι := ι) n)
  rw [hX] at h
  exact congrArg (fun A : Matrix ι ι ℂ => A i j) h

def m1b_adjugateNumerator (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) :
    MvPolynomial ((ι × ι) ⊕ (Fin n × ι)) ℂ :=
  ∑ a : Fin n → ι, MvPolynomial.C (f (fun i => Pi.single (a i) 1)) *
    ∏ i, ∑ j, (m1b_matrixVariables (ι := ι) n).adjugate (a i) j *
      MvPolynomial.X (Sum.inr (i, j))

theorem m1b_adjugateNumerator_eval
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (M : Matrix ι ι ℂ) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (Sum.elim (fun p : ι × ι => M p.1 p.2)
      (fun p : Fin n × ι => v p.1 p.2)) (m1b_adjugateNumerator f) =
      f (fun i => M.adjugate *ᵥ v i) := by
  rw [m1b_multilinear_coordinate_expansion f (fun i => M.adjugate *ᵥ v i)]
  simp only [m1b_adjugateNumerator, map_sum, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, m1b_adjugateVariables_eval, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem m1b_adjugateNumerator_inverse
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (M : Matrix ι ι ℂ) (hM : IsUnit M) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (Sum.elim (fun p : ι × ι => M p.1 p.2)
      (fun p : Fin n × ι => v p.1 p.2)) (m1b_adjugateNumerator f) =
      M.det ^ n * f (fun i => M⁻¹ *ᵥ v i) := by
  rw [m1b_adjugateNumerator_eval]
  exact m1b_multilinear_adjugate_denominator f M hM v

theorem m1b_multilinear_coordinate_expansion_module {M : Type*}
    [AddCommGroup M] [Module ℂ M]
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) M) (v : Fin n → ι → ℂ) :
    f v = ∑ a : Fin n → ι, (∏ i, v i (a i)) • f (fun i => Pi.single (a i) 1) := by
  classical
  have hv (i : Fin n) : v i = ∑ j, v i j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply, apply_ite]
  calc
    f v = f (fun i => ∑ j, v i j • Pi.single j (1 : ℂ)) := congrArg f (funext hv)
    _ = ∑ a : Fin n → ι, f (fun i => v i (a i) • Pi.single (a i) (1 : ℂ)) :=
      f.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact f.map_smul_univ _ _

end HodgeLean.Foundations.Program
