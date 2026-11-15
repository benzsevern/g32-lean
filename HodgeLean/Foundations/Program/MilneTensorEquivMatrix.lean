import HodgeLean.Foundations.Program.MilneTensorMatrixOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_linearEquiv_matrix_data (B : Matrix ι ι ℂ)
    (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) :
    ∃ M : Matrix ι ι ℂ, M.det ≠ 0 ∧ (∀ v, M⁻¹ *ᵥ v = e.symm v) ∧
      ∀ i j, (M⁻¹.transpose * B * M⁻¹) i j =
        m1b_formTransport B.toBilin' e (Pi.single i 1) (Pi.single j 1) := by
  let M := LinearMap.toMatrix' e.toLinearMap
  let N := LinearMap.toMatrix' e.symm.toLinearMap
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      funext i
      change e.symm (e v) i = v i
      rw [LinearEquiv.symm_apply_apply]
    rw [he, LinearMap.toMatrix'_id]
  have hN : M⁻¹ = N := Matrix.inv_eq_left_inv hNM
  refine ⟨M, Matrix.det_ne_zero_of_left_inverse hNM, ?_, ?_⟩
  · intro v
    rw [hN]
    exact LinearMap.toMatrix'_mulVec e.symm.toLinearMap v
  · intro i j
    have he : (M⁻¹.transpose * B * M⁻¹).toBilin' = m1b_formTransport B.toBilin' e := by
      rw [hN, ← Matrix.toBilin'_comp]
      change B.toBilin'.comp (Matrix.toLin' (LinearMap.toMatrix' e.symm.toLinearMap))
        (Matrix.toLin' (LinearMap.toMatrix' e.symm.toLinearMap)) = _
      rw [Matrix.toLin'_toMatrix']
      rfl
    rw [← he]
    exact (Matrix.toBilin'_single _ i j).symm

theorem m1b_matrix_polynomial_linearEquiv {r n : ℕ} (B : Matrix ι ι ℂ)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hp : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
      MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
        (fun tc => v tc.1 tc.2.1 tc.2.2)) p = f (fun j c => M⁻¹ *ᵥ v j c)) :
    ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B.toBilin' e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) p = f (fun j c => e.symm (v j c)) := by
  intro e v
  obtain ⟨M, hM, hi, hform⟩ := m1b_linearEquiv_matrix_data B e
  simpa only [hi, hform] using hp M hM v

end HodgeLean.Foundations.Program
