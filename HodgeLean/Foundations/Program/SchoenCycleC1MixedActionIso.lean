import HodgeLean.Foundations.Program.SchoenCycleRetainedAction

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every specified mixed coordinate action is an actual scheme isomorphism;
its inverse translates by the negative permuted vector. -/
theorem s2e_c1_mixed_action_isIso
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)) :
    IsIso (s2_action S Y a e N v σ) := by
  obtain ⟨h1, hmul⟩ := s2e_retained_coordinate_laws S Y a e ha1 hamul N
  refine ⟨⟨s2_action S Y a e N (fun i => -v (σ i)) σ⁻¹, ?_, ?_⟩⟩
  · rw [hmul]
    have hv : (fun i => -v (σ i) + v ((σ⁻¹).symm i)) = 0 := by funext i; simp [Equiv.Perm.inv_def]
    rw [hv, inv_mul_cancel]
    exact h1
  · rw [hmul]
    have hv : (fun i => v i + -v (σ (σ.symm i))) = 0 := by funext i; simp [Equiv.Perm.inv_def]
    rw [hv, mul_inv_cancel]
    exact h1

end HodgeLean.Foundations.Program
