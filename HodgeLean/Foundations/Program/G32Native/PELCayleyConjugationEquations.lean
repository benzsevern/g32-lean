import HodgeLean.Foundations.Program.G32Native.PELCayleyPolynomialChart

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations
open MvPolynomial MatrixCayley
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Conjugation in a Cayley chart has a common polynomial denominator. -/
theorem pel_cayley_conjugation_numerators
    (X : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ι → ℂ)
    (hz : eval z ((1 - X).det * (1 + X).det) ≠ 0) (i j : Fin n) :
    eval z ((((1 + X) * (1 - X).adjugate) * A.map (fun a => (C a : MvPolynomial ι ℂ)) *
      ((1 - X) * (1 + X).adjugate)) i j) =
      eval z ((1 - X).det * (1 + X).det) *
        (cayley (-((eval z).mapMatrix X)) * A *
          cayley ((eval z).mapMatrix X)) i j := by
  classical
  have hminus : eval z (1 - X).det ≠ 0 :=
    (mul_ne_zero_iff.mp (by simpa only [map_mul] using hz)).1
  have hplus : eval z (1 + X).det ≠ 0 :=
    (mul_ne_zero_iff.mp (by simpa only [map_mul] using hz)).2
  have hm : (eval z).mapMatrix ((1 + X) * (1 - X).adjugate) =
      eval z (1 - X).det • cayley (-((eval z).mapMatrix X)) := by
    have hneg : eval z (1 + (-X)).det ≠ 0 := by
      simpa only [sub_eq_add_neg] using hminus
    ext a b
    have h := pel_cayley_polynomial_numerators (-X) z hneg a b
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, map_neg, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul] using h
  have hp : (eval z).mapMatrix ((1 - X) * (1 + X).adjugate) =
      eval z (1 + X).det • cayley ((eval z).mapMatrix X) := by
    ext a b
    exact pel_cayley_polynomial_numerators X z hplus a b
  have hA : (eval z).mapMatrix (A.map (fun a => (C a : MvPolynomial ι ℂ))) = A := by
    ext a b
    simp
  have he : (eval z).mapMatrix
      (((1 + X) * (1 - X).adjugate) * A.map (fun a => (C a : MvPolynomial ι ℂ)) *
        ((1 - X) * (1 + X).adjugate)) =
      eval z ((1 - X).det * (1 + X).det) •
        (cayley (-((eval z).mapMatrix X)) * A *
          cayley ((eval z).mapMatrix X)) := by
    rw [map_mul, map_mul, hm, hp, hA]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul]
    rw [mul_comm]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) he

/-- Equations on Cayley conjugates extend from a real neighborhood to every
complex parameter where both chart denominators are nonzero. -/
theorem pel_cayley_conjugation_equation_of_real_nhds
    (X : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (a : ι → ℝ)
    (hdet : ∀ᶠ t in nhds a,
      eval (fun i => (t i : ℂ)) ((1 - X).det * (1 + X).det) ≠ 0)
    (hp : ∀ᶠ t in nhds a,
      eval (fun ij : Fin n × Fin n =>
        (cayley (-((eval (fun i => (t i : ℂ))).mapMatrix X)) * A *
          cayley ((eval (fun i => (t i : ℂ))).mapMatrix X)) ij.1 ij.2) p = 0) :
    ∀ z, eval z ((1 - X).det * (1 + X).det) ≠ 0 →
      eval (fun ij : Fin n × Fin n =>
        (cayley (-((eval z).mapMatrix X)) * A *
          cayley ((eval z).mapMatrix X)) ij.1 ij.2) p = 0 := by
  exact pel_rational_equation_of_real_nhds ((1 - X).det * (1 + X).det)
    (fun ij : Fin n × Fin n =>
      (((1 + X) * (1 - X).adjugate) * A.map (fun a => (C a : MvPolynomial ι ℂ)) *
        ((1 - X) * (1 + X).adjugate)) ij.1 ij.2)
    (fun z ij => (cayley (-((eval z).mapMatrix X)) * A *
      cayley ((eval z).mapMatrix X)) ij.1 ij.2)
    (fun z hz ij => pel_cayley_conjugation_numerators X A z hz ij.1 ij.2)
    p a hdet hp

#print axioms pel_cayley_conjugation_numerators
#print axioms pel_cayley_conjugation_equation_of_real_nhds
end HodgeLean.Foundations
