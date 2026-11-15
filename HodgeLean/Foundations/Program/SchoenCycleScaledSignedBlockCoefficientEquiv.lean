import HodgeLean.Foundations.Program.SchoenCycleEtaleAnalyticChartDescent
import Mathlib.Data.Fin.Rev

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Scaled signed reverse indexing of each elementary block is an actual complex continuous linear equivalence on the original indexed coordinate space.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_scaled_signed_block_coefficient_equiv
    (n b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (c : ℂ) (hc : c ≠ 0) :
    ∃ L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      ∀ (v : Fin n → ℂ) (a : Fin b) (j : Fin (m a)),
        L v (ι ⟨a, j⟩) = ((-1 : ℂ) ^ (m a - j.val) * c ^ (m a - j.val)) * v (ι ⟨a, j.rev⟩) := by
  classical
  let r : Fin n ≃ Fin n :=
    (ι.symm.trans (Equiv.Perm.sigmaCongrRight (fun a => Fin.revPerm))).trans ι
  let s (i : Fin n) : ℂ := (-1 : ℂ) ^ (m (ι.symm i).1 - (ι.symm i).2.val) *
    c ^ (m (ι.symm i).1 - (ι.symm i).2.val)
  have hs (i : Fin n) : s i ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hc)
  let F : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun v i => s i * v (r i)
    map_add' := by intro v w; funext i; exact mul_add _ _ _
    map_smul' := by intro c v; funext i; exact mul_left_comm _ _ _ }
  have hF : Function.Bijective F := by
    constructor
    · intro v w h
      funext i
      have he := congrFun h (r.symm i)
      change s (r.symm i) * v (r (r.symm i)) = s (r.symm i) * w (r (r.symm i)) at he
      rw [r.apply_symm_apply] at he
      exact mul_left_cancel₀ (hs _) he
    · intro v
      refine ⟨fun i => (s (r.symm i))⁻¹ * v (r.symm i), ?_⟩
      funext i
      change s i * ((s (r.symm (r i)))⁻¹ * v (r.symm (r i))) = v i
      rw [r.symm_apply_apply, ← mul_assoc, mul_inv_cancel₀ (hs i), one_mul]
  refine ⟨(LinearEquiv.ofBijective F hF).toContinuousLinearEquiv, ?_⟩
  intro v a j
  change s (ι ⟨a, j⟩) * v (r (ι ⟨a, j⟩)) = _
  have hs' : s (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) * c ^ (m a - j.val) := by
    dsimp only [s]
    rw [ι.symm_apply_apply]
  have hr : r (ι ⟨a, j⟩) = ι ⟨a, j.rev⟩ := by
    dsimp only [r, Equiv.trans_apply]
    rw [ι.symm_apply_apply]
    rfl
  rw [hs', hr]

#print axioms s2e_scaled_signed_block_coefficient_equiv
end HodgeLean.Foundations.Program
