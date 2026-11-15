import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

/-! # Projection from indexed collision-block lifts -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Projection of the actual indexed lift recovers the specified block entry.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_indexed_cluster_lift_projection
    {T Y : Over (Spec ↧ℂ)} {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (f : (a : Fin b) → Fin (m a) → (T ⟶ Y)) (a : Fin b) (i : Fin (m a)) :
    s2_lift n (fun j => f (ι.symm j).1 (ι.symm j).2) ≫ g3_proj Y n (ι ⟨a, i⟩) = f a i := by
  rw [s2_check_lift_proj]
  exact congrArg (fun v : Σ a, Fin (m a) => f v.1 v.2) (ι.symm_apply_apply ⟨a, i⟩)

#print axioms s2e_indexed_cluster_lift_projection
end HodgeLean.Foundations.Program
