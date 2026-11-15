import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Complex.Basic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b66d_dual_integral_ext {L : Type*} [AddCommGroup L]
    (f g : (ℂ ⊗[ℤ] L) →ₗ[ℂ] ℂ)
    (h : ∀ x : L, f (1 ⊗ₜ[ℤ] x) = g (1 ⊗ₜ[ℤ] x)) : f = g := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul z x =>
    have hz : z ⊗ₜ[ℤ] x = z • (1 ⊗ₜ[ℤ] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, map_smul, h]

theorem b66d_eigen_coefficients {ι X : Type*} [Fintype ι]
    (f : ι → X → ℂ) (hf : LinearIndependent ℂ f) (A : X → X)
    (e : ι → ℂ) (he : ∀ i x, f i (A x) = e i * f i x)
    (a : ι → ℂ) (z : ℂ)
    (ha : ∀ x, (∑ i, a i • f i) (A x) = z * (∑ i, a i • f i) x) :
    ∀ i, (e i - z) * a i = 0 := by
  apply (Fintype.linearIndependent_iff.mp hf) (fun i => (e i - z) * a i)
  funext x
  have hx := ha x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  calc
    (∑ i, (e i - z) * a i * f i x) =
        (∑ i, a i * f i (A x)) - z * (∑ i, a i * f i x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [he]
      ring
    _ = 0 := by rw [hx]; ring

end HodgeLean.Foundations.Program
