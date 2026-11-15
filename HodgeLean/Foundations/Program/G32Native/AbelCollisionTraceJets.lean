import HodgeLean.Foundations.Program.G32Native.AbelCollisionDescendedTrace
import HodgeLean.Foundations.Program.G32Native.AbelCollisionPrimitiveJets
import Mathlib.LinearAlgebra.StdBasis

/-! # The full jet detected by a descended primitive trace -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Coordinate directional derivatives detect the entire derivative functional. -/
theorem collision_fderiv_zero_iff {m : ℕ} (f : (Fin m → ℂ) → ℂ) :
    fderiv ℂ f 0 = 0 ↔ ∀ j : Fin m, fderiv ℂ f 0 (Pi.single j 1) = 0 := by
  classical
  constructor
  · intro h j
    rw [h]
    rfl
  · intro h
    have hl : (fderiv ℂ f 0).toLinearMap = (0 : (Fin m → ℂ) →ₗ[ℂ] ℂ) := by
      apply (Pi.basisFun ℂ (Fin m)).ext
      intro j
      change fderiv ℂ f 0 ((Pi.basisFun ℂ (Fin m)) j) = 0
      simpa only [Pi.basisFun_apply] using h j
    ext v
    exact congrArg (fun L : (Fin m → ℂ) →ₗ[ℂ] ℂ => L v) hl


/-- A zero trace derivative is precisely vanishing of all primitive coefficients required by the block. -/
theorem collision_descended_trace_coefficient_kernel {m : ℕ}
    (f : (Fin m → ℂ) → ℂ) (H : ℂ → ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hp : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ),
      f (collisionMonicCoefficients z) = (∑ i, H (z i)) + c) :
    fderiv ℂ f 0 = 0 ↔ ∀ k < m, p.coeff (k + 1) = 0 := by
  rw [collision_fderiv_zero_iff]
  have hd (j : Fin m) : fderiv ℂ f 0 (Pi.single j 1) = 0 ↔ p.coeff (m - j.val) = 0 := by
    rw [collision_descended_trace_derivative_at_index j f H p hf hp c he]
    have hn : ((m - j.val : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt j.isLt)
    simp only [mul_eq_zero, neg_eq_zero, hn, false_or]
  simp_rw [hd]
  constructor
  · intro h k hk
    have hj := h (⟨k, hk⟩ : Fin m).rev
    have hn : m - (⟨k, hk⟩ : Fin m).rev.val = k + 1 := by
      rw [Fin.val_rev]
      change m - (m - (k + 1)) = k + 1
      omega
    rwa [hn] at hj
  · intro h j
    have hn : m - j.val = j.rev.val + 1 := by rw [Fin.val_rev]; omega
    rw [hn]
    exact h _ j.rev.isLt

/-- The trace derivative detects the full multiplicity order of the original differential. -/
theorem collision_descended_trace_jet_kernel {m : ℕ}
    (f : (Fin m → ℂ) → ℂ) (H : ℂ → ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hp : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ),
      f (collisionMonicCoefficients z) = (∑ i, H (z i)) + c) :
    fderiv ℂ f 0 = 0 ↔ (m : ℕ∞) ≤ analyticOrderAt (deriv H) 0 :=
  (collision_descended_trace_coefficient_kernel f H p hf hp c he).trans
    (collision_primitive_jet_iff hp m)

#print axioms collision_fderiv_zero_iff
#print axioms collision_descended_trace_coefficient_kernel
#print axioms collision_descended_trace_jet_kernel
end HodgeLean.Foundations.Program.G32Native
