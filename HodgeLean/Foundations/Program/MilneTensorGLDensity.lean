import HodgeLean.Foundations.Program.MilneTensorGLDenominator
import HodgeLean.Foundations.Program.MilneTensorRationalExtension

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_symbolic_GL_extension_from_pivot {σ : Type*} {r n : ℕ}
    (T : Matrix ι ι (MvPolynomial σ ℂ)) (B : Matrix ι ι ℂ)
    (v : Fin n → Fin r → ι → MvPolynomial σ ℂ)
    (pF : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (pV : MvPolynomial (Fin n × (Fin r × ι)) ℂ) (i₀ j₀ : ι)
    (hd : T.det ≠ 0)
    (hp : (T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) * T.adjugate) i₀ j₀ ≠ 0)
    (hlocal : ∀ x, MvPolynomial.eval x T.det ≠ 0 →
      ((((MvPolynomial.eval x).mapMatrix T)⁻¹).transpose * B *
        ((MvPolynomial.eval x).mapMatrix T)⁻¹) i₀ j₀ ≠ 0 →
      MvPolynomial.eval
        (Sum.elim (fun ij => ((((MvPolynomial.eval x).mapMatrix T)⁻¹).transpose * B *
          ((MvPolynomial.eval x).mapMatrix T)⁻¹) ij.1 ij.2)
          (fun jc => MvPolynomial.eval x (v jc.1 jc.2.1 jc.2.2))) pF =
        MvPolynomial.eval (fun jc => (((MvPolynomial.eval x).mapMatrix T)⁻¹ *ᵥ
          (fun i => MvPolynomial.eval x (v jc.1 jc.2.1 i))) jc.2.2) pV) :
    ∀ x, MvPolynomial.eval x T.det ≠ 0 →
      MvPolynomial.eval
        (Sum.elim (fun ij => ((((MvPolynomial.eval x).mapMatrix T)⁻¹).transpose * B *
          ((MvPolynomial.eval x).mapMatrix T)⁻¹) ij.1 ij.2)
          (fun jc => MvPolynomial.eval x (v jc.1 jc.2.1 jc.2.2))) pF =
        MvPolynomial.eval (fun jc => (((MvPolynomial.eval x).mapMatrix T)⁻¹ *ᵥ
          (fun i => MvPolynomial.eval x (v jc.1 jc.2.1 i))) jc.2.2) pV := by
  obtain ⟨k, a, ha⟩ := m1b_form_polynomial_GL_denominator T B v pF
  obtain ⟨l, b, hb⟩ := m1b_vector_polynomial_GL_denominator T v pV
  apply m1b_principal_open_rational_extension T.det
    ((T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) * T.adjugate) i₀ j₀) a b hd hp k l
    _ _ (fun x hx => (ha x hx).symm) (fun x hx => (hb x hx).symm)
  intro x hx hpx
  apply hlocal x hx
  intro hz
  apply hpx
  rw [m1b_eval_adjugate_congruence]
  have hm : ((MvPolynomial.eval x).mapMatrix T).det ≠ 0 := by
    rw [← (MvPolynomial.eval x).map_det T]
    exact hx
  have hs := congrArg (fun M : Matrix ι ι ℂ => M i₀ j₀)
    (m1b_inverse_congruence_denominator ((MvPolynomial.eval x).mapMatrix T) B hm)
  rw [← hs]
  change ((MvPolynomial.eval x).mapMatrix T).det ^ 2 *
    ((((MvPolynomial.eval x).mapMatrix T)⁻¹).transpose * B *
      ((MvPolynomial.eval x).mapMatrix T)⁻¹) i₀ j₀ = 0
  rw [hz, mul_zero]

set_option maxHeartbeats 400000 in
theorem m1b_polynomial_orbit_extension_of_local {r n : ℕ}
    (B : Matrix ι ι ℂ)
    (pF : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (pV : MvPolynomial (Fin n × (Fin r × ι)) ℂ) (i₀ j₀ : ι) (hB : B i₀ j₀ ≠ 0)
    (hlocal : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → (M⁻¹.transpose * B * M⁻¹) i₀ j₀ ≠ 0 →
      ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
          (fun jc => v jc.1 jc.2.1 jc.2.2)) pF =
          MvPolynomial.eval (fun jc => (M⁻¹ *ᵥ v jc.1 jc.2.1) jc.2.2) pV) :
    ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
      MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
        (fun jc => v jc.1 jc.2.1 jc.2.2)) pF =
        MvPolynomial.eval (fun jc => (M⁻¹ *ᵥ v jc.1 jc.2.1) jc.2.2) pV := by
  let σ := (ι × ι) ⊕ (Fin n × (Fin r × ι))
  let T : Matrix ι ι (MvPolynomial σ ℂ) := fun i j => MvPolynomial.X (Sum.inl (i, j))
  let w : Fin n → Fin r → ι → MvPolynomial σ ℂ :=
    fun j c i => MvPolynomial.X (Sum.inr (j, c, i))
  let x₀ : σ → ℂ := Sum.elim (fun ij => (1 : Matrix ι ι ℂ) ij.1 ij.2) (fun _ => 0)
  have hT₀ : (MvPolynomial.eval x₀).mapMatrix T = 1 := by
    ext i j
    change MvPolynomial.eval x₀ (MvPolynomial.X (Sum.inl (i, j))) = (1 : Matrix ι ι ℂ) i j
    exact MvPolynomial.eval_X _
  have hd : T.det ≠ 0 := by
    intro hz
    have h := congrArg (MvPolynomial.eval x₀) hz
    rw [map_zero, (MvPolynomial.eval x₀).map_det T, hT₀, Matrix.det_one] at h
    exact one_ne_zero h
  have hp : (T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) *
      T.adjugate) i₀ j₀ ≠ 0 := by
    intro hz
    have h := congrArg (MvPolynomial.eval x₀) hz
    rw [map_zero, m1b_eval_adjugate_congruence, hT₀, Matrix.adjugate_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
    exact hB h
  have hglobal := m1b_symbolic_GL_extension_from_pivot T B w pF pV i₀ j₀ hd hp (by
    intro x hx hpx
    have hm : ((MvPolynomial.eval x).mapMatrix T).det ≠ 0 := by
      rw [← (MvPolynomial.eval x).map_det T]
      exact hx
    exact hlocal ((MvPolynomial.eval x).mapMatrix T) hm hpx
      (fun j c i => MvPolynomial.eval x (w j c i)))
  intro M hM v
  let x : σ → ℂ := Sum.elim (fun ij => M ij.1 ij.2) (fun jc => v jc.1 jc.2.1 jc.2.2)
  have hT : (MvPolynomial.eval x).mapMatrix T = M := by
    ext i j
    change MvPolynomial.eval x (MvPolynomial.X (Sum.inl (i, j))) = M i j
    exact MvPolynomial.eval_X _
  have hw (j : Fin n) (c : Fin r) (i : ι) : MvPolynomial.eval x (w j c i) = v j c i :=
    MvPolynomial.eval_X _
  have h := hglobal x (by rw [(MvPolynomial.eval x).map_det T, hT]; exact hM)
  simpa only [hT, hw] using h

end HodgeLean.Foundations.Program
