import HodgeLean.Foundations.Program.MilneTensorSymmetricInduction
import HodgeLean.Foundations.Program.MilneTensorEquivMatrix

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_standard_symmetric_successor {d r n : ℕ} (hd : 0 < d)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Unit ⊕ Fin d → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin',
      ∀ v, f (fun t => m1b_copies r u (v t)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin',
        ∀ v, g (fun t => m1b_copies r u (v t)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' e
              (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun t c => e.symm (v t c))) :
    ∃ P : MvPolynomial (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Unit ⊕ Fin d)))) ℂ,
      ∀ (e : (Unit ⊕ Fin d → ℂ) ≃ₗ[ℂ] (Unit ⊕ Fin d → ℂ))
        (v : Fin n → Fin r → Unit ⊕ Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin'
              e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)) := by
  let c := m1b_scalarCoordinates d
  let Bp := m1b_prodBilin (LinearMap.mul ℂ ℂ) (1 : Matrix (Fin d) (Fin d) ℂ).toBilin'
  let g := f.compLinearMap (fun _ => (m1b_copiesEquiv c r).symm.toLinearMap)
  have hBp : (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin'.compl₁₂
      c.symm.toLinearMap c.symm.toLinearMap = Bp := by
    rw [← m1b_scalarCoordinates_standard d]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Bp (c (c.symm x)) (c (c.symm y)) = Bp x y
    simp only [LinearEquiv.apply_symm_apply]
  have hg : ∀ u ∈ m1b_isometries Bp, ∀ v,
      g (fun t => m1b_copies r u (v t)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport c
      (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin' f hf u _ v
    rwa [hBp]
  obtain ⟨P, hP⟩ := m1b_standard_symmetric_induction_step hd g hg hsmall
  refine ⟨P, m1b_matrix_polynomial_linearEquiv
    (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ) f P ?_⟩
  intro M hM v
  have h := hP M hM v
  change MvPolynomial.eval _ P =
    f (fun t a => c.symm (c (M⁻¹ *ᵥ v t a))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end HodgeLean.Foundations.Program
