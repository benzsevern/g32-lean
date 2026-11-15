import HodgeLean.Foundations.Program.MilneTensorScalarMatrixNumerator
import HodgeLean.Foundations.Program.MilneTensorInvariantAssembly
import HodgeLean.Foundations.Program.MilneTensorProductForm

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_standard_symmetric_induction_step {d r n : ℕ} (hd : 0 < d)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ℂ × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries
      (m1b_prodBilin (LinearMap.mul ℂ ℂ) (1 : Matrix (Fin d) (Fin d) ℂ).toBilin'),
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
      ∀ M : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ, M.det ≠ 0 →
        ∀ v : Fin n → Fin r → Unit ⊕ Fin d → ℂ,
          MvPolynomial.eval (Sum.elim
            (fun ij => (M⁻¹.transpose * (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ) * M⁻¹) ij.1 ij.2)
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P =
              f (fun t c => m1b_scalarCoordinates d (M⁻¹ *ᵥ v t c)) := by
  let B := (1 : Matrix (Fin d) (Fin d) ℂ).toBilin'
  let Bp := m1b_prodBilin (LinearMap.mul ℂ ℂ) B
  have hB : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  have hsB (x y : Fin d → ℂ) : B x y = B y x := by
    change (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' x y =
      (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' y x
    simp only [Matrix.toBilin'_apply', Matrix.one_mulVec]
    exact dotProduct_comm x y
  have hA : (LinearMap.mul ℂ ℂ).Nondegenerate := by
    constructor <;> intro x hx
    · simpa using hx 1
    · simpa using hx 1
  have hBp := m1b_prodBilin_nondegenerate (LinearMap.mul ℂ ℂ) B hA hB
  have hsBp (x y : ℂ × (Fin d → ℂ)) : Bp x y = Bp y x := by
    change x.1 * y.1 + B x.2 y.2 = y.1 * x.1 + B y.2 x.2
    rw [mul_comm x.1 y.1, hsB]
  obtain ⟨k, q, hq⟩ := m1b_symmetric_scalar_orbit_numerator B hB hsB f hf hsmall
  have hqt := m1b_scalar_numerator_on_all_forms Bp hBp hsBp f k q hq
  have hqm := m1b_scalar_matrix_numerator Bp hBp hsBp f hf k q hqt
  have hC : Bp.compl₁₂ (m1b_scalarCoordinates d).toLinearMap
      (m1b_scalarCoordinates d).toLinearMap =
        (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin' :=
    m1b_scalarCoordinates_standard d
  rw [hC] at hqm
  let g := f.compLinearMap (fun _ =>
    (m1b_copiesEquiv (m1b_scalarCoordinates d).symm r).symm.toLinearMap)
  have hg : ∀ u ∈ m1b_isometries (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ).toBilin',
      ∀ v, g (fun t => m1b_copies r u (v t)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport (m1b_scalarCoordinates d).symm Bp f hf u _ v
    simpa only [LinearEquiv.symm_symm, hC] using hu
  obtain ⟨P, hP⟩ := m1b_symmetric_orbit_polynomial_from_numerator
    (1 : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ)
    (fun s t => by simp [Matrix.one_apply, eq_comm]) (by simp)
    (Sum.inl ()) (Sum.inr ⟨0, hd⟩) (by intro h; cases h) (by simp)
    g hg q k hqm
  refine ⟨P, ?_⟩
  intro M hM v
  exact hP M hM v

end HodgeLean.Foundations.Program
