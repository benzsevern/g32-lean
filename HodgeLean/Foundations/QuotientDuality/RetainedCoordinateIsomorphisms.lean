import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

/-! Actual algebraic isomorphisms for the retained coordinate transformations. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ)

def retainedCoordinateIso (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)) :
    g3_power Y n ≅ g3_power Y n where
  hom := s2_action S Y a e n v σ
  inv := s2_action S Y a e n (fun i => -v (σ i)) σ⁻¹
  hom_inv_id := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul n).2, inv_mul_cancel]
    have hz : (fun i => -v (σ i) + v ((σ⁻¹).symm i)) = 0 := by
      funext i
      simp [Equiv.Perm.inv_def]
    rw [hz]
    exact (s2_coordinateAction_laws S Y a e ha1 hamul n).1
  inv_hom_id := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul n).2, mul_inv_cancel]
    have hz : (fun i => v i + -v (σ (σ.symm i))) = 0 := by
      funext i
      simp
    rw [hz]
    exact (s2_coordinateAction_laws S Y a e ha1 hamul n).1

#print axioms retainedCoordinateIso
end HodgeLean.Foundations.QuotientDuality
