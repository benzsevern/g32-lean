import HodgeLean.Foundations.Program.MilneTensorPairSums
import HodgeLean.Foundations.Program.MilneTensorPairEvaluation
import HodgeLean.Foundations.Program.MilneTensorPolarizedUnits
import HodgeLean.Foundations.Program.MilneTensorPairingEquiv
import HodgeLean.Foundations.Program.MilneTensorMatrixPairFunction
import HodgeLean.Foundations.Program.MilneTensorProductsMono

noncomputable section
open Matrix
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_tensor_mem_products_of_polarization
    (B : LinearMap.BilinForm ℂ (ι → ℂ)) (hB : B.Nondegenerate) (k : ℕ)
    (t : ⨂[ℂ]^(k * 2) (ι → ℂ))
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (hJ : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v q,
      J v (fun a => m1b_congruenceCoordinates M (q a)) = J (fun s => M *ᵥ v s) q)
    (hdiag : ∀ v, J v (fun _ ij => B (Pi.single ij.1 1) (Pi.single ij.2 1)) =
      m1b_tensorFunction B (k * 2) t v) :
    t ∈ m1b_products (m1b_fixed (m1b_isometries B) 2) (k * 2) := by
  let C := (1 : Matrix ι ι ℂ).toBilin'
  have hC : C.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  let Q : Matrix ι ι ℂ := Matrix.toBilin'.symm B
  have hQ : Q.toBilin' = B := Matrix.toBilin'.apply_symm_apply B
  have hQij : ∀ i j, Q i j = B (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    rw [← hQ, Matrix.toBilin'_single]
  let b : ⨂[ℂ]^2 (ι → ℂ) := ∑ ij : ι × ι, ⨂ₜ[ℂ] s, m1b_matrixPairVectors Q ij s
  let R : Submodule ℂ (⨂[ℂ]^2 (ι → ℂ)) := Submodule.span ℂ {b}
  let T : ⨂[ℂ]^(k * 2) (ι → ℂ) := ∑ f : Fin k → ι × ι,
    ⨂ₜ[ℂ] s, m1b_matrixPairVectors Q (f (finProdFinEquiv.symm s).1)
      (finProdFinEquiv.symm s).2
  have hT : T ∈ m1b_products R (k * 2) :=
    m1b_products_pairSums R k (fun _ => m1b_matrixPairVectors Q)
      (fun _ => Submodule.subset_span (Set.mem_singleton b)) finProdFinEquiv
  let F := m1b_polarizedTensorMap C hC k J
  have hFT : F T ∈ m1b_products R (k * 2) :=
    m1b_products_commutant R (k * 2) F (m1b_polarizedTensorMap_unit_commutes hC k J hJ) T hT
  have hfun : m1b_tensorFunction C (k * 2) (F T) = m1b_tensorFunction B (k * 2) t := by
    apply MultilinearMap.ext
    intro v
    change m1b_tensorFunction C (k * 2)
      (m1b_polarizedTensorMap C hC k J _) v = _
    rw [m1b_polarizedTensorMap_pairSum C hC k J (fun _ => m1b_matrixPairVectors Q) v,
      m1b_matrixPairVectors_sum]
    simpa only [hQij] using hdiag v
  let e := m1b_pairingChangeEquiv C B hC hB
  have he : ∀ x y, B (e x) y = C x y := m1b_pairingChangeEquiv_apply C B hC hB
  have hrecover : m1b_tensorEquiv e (k * 2) (F T) = t := by
    apply m1b_tensorFunction_injective B hB (k * 2)
    exact (m1b_tensorFunction_pairing_change C B (k * 2) e.toLinearMap he (F T)).trans hfun
  have hR : R.map (m1b_tensorEquiv e 2).toLinearMap ≤ m1b_fixed (m1b_isometries B) 2 := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro z (rfl : z = b)
    apply (m1b_tensorFunction_fixed_iff B hB 2 (m1b_isometries B) (fun _ h => h) _).mpr
    intro u hu v
    have hh := m1b_tensorFunction_pairing_change C B 2 e.toLinearMap he b
    change m1b_tensorFunction B 2 (m1b_tensorEquiv e 2 b) =
      m1b_tensorFunction C 2 b at hh
    change m1b_tensorFunction B 2 (m1b_tensorEquiv e 2 b) (fun i => u (v i)) =
      m1b_tensorFunction B 2 (m1b_tensorEquiv e 2 b) v
    rw [hh]
    change m1b_tensorFunction (1 : Matrix ι ι ℂ).toBilin' 2 b _ = _
    dsimp only [b]
    rw [m1b_matrixPairVectors_tensorFunction, m1b_matrixPairVectors_tensorFunction, hQ]
    exact hu.2 (v 0) (v 1)
  have hm := m1b_products_transport e R (k * 2) (F T) hFT
  rw [hrecover] at hm
  exact m1b_products_mono _ _ hR (k * 2) hm

end HodgeLean.Foundations.Program
