import HodgeLean.Foundations.Program.MilneTensorCovariantPolynomial
import HodgeLean.Foundations.Program.MilneTensorJointCovariance
import HodgeLean.Foundations.Program.MilneTensorOrbitPolarization

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_covariant_polarization_of_orbit_polynomial
    (ε : ℂ) (hε : ε ^ 2 = 1)
    (B : LinearMap.BilinForm ℂ (ι → ℂ)) (hB : B.Nondegenerate)
    (hsign : ∀ x y, B y x = ε * B x y) (k : ℕ)
    (f : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun s => u (v s)) = f v)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin (k * 2) × (Fin 1 × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin (k * 2) → Fin 1 → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun s => e.symm (v s 0)))
    (horbit : ∀ Q : Matrix ι ι ℂ, Q.det ≠ 0 → Q.transpose = ε • Q →
      Q.toBilin' ∈ Set.range (m1b_formTransport B)) :
    ∃ J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ),
      (∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v q,
        J v (fun a => m1b_congruenceCoordinates M (q a)) = J (fun s => M *ᵥ v s) q) ∧
      (∀ v, J v (fun _ ij => B (Pi.single ij.1 1) (Pi.single ij.2 1)) = f v) := by
  let Q : Matrix ι ι ℂ := Matrix.toBilin'.symm B
  have hQ : Q.toBilin' = B := Matrix.toBilin'.apply_symm_apply B
  have hQij : ∀ i j, Q i j = B (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    rw [← hQ, Matrix.toBilin'_single]
  have hQs : Q.transpose = ε • Q := by
    ext i j
    change Q j i = ε * Q i j
    simp only [hQij]
    exact hsign _ _
  have hdet : (m1b_matrixFormProjection ε Q).det ≠ 0 := by
    rw [m1b_matrixFormProjection_fixed ε hε Q hQs]
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
    rwa [hQ]
  let f₁ : MultilinearMap ℂ (fun _ : Fin (k * 2) => Fin 1 → ι → ℂ) ℂ :=
    f.compLinearMap (fun _ => LinearMap.proj (0 : Fin 1))
  have hf₁ : ∀ u ∈ m1b_isometries B, ∀ v,
      f₁ (fun s => m1b_copies 1 u (v s)) = f₁ v := by
    intro u hu v
    exact hf u hu (fun s => v s 0)
  obtain ⟨R, hR, hrec, hcov⟩ := m1b_reconstructed_projected_orbit_polynomial
    ε hε Q hdet B hsign f₁ hf₁ P hP horbit
  let L : (ι → ℂ) →ₗ[ℂ] (Fin 1 × ι → ℂ) := LinearMap.pi (fun ci => LinearMap.proj ci.2)
  let J := (m1b_jointPolarization k R).compLinearMap (fun _ => L)
  refine ⟨J, ?_, ?_⟩
  · intro M hM v q
    exact m1b_jointPolarization_covariance k (m1b_congruenceCoordinates M)
      (m1b_repeatedVectorMap 1 (k * 2) M) R hrec (hcov M hM) (fun s => L (v s)) q
  · intro v
    exact m1b_jointPolarization_orbit_diagonal B f₁ R hR hrec (fun s _ => v s)

end HodgeLean.Foundations.Program
