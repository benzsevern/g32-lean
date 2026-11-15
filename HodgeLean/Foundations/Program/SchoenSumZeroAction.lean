import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every retained coordinate action has its explicit inverse as an actual scheme-product automorphism. -/
def s2_coordinateActionIso (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)) :
    g3_power Y h ≅ g3_power Y h where
  hom := s2_action S Y a e h v σ
  inv := s2_action S Y a e h (fun i => -v (σ i)) σ⁻¹
  hom_inv_id := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul h).2]
    have hz : (fun i => -v (σ i) + v ((σ⁻¹).symm i)) = 0 := by
      funext i
      simp only [Equiv.Perm.inv_def, Equiv.symm_symm, neg_add_cancel, Pi.zero_apply]
    rw [hz, inv_mul_cancel]
    exact (s2_coordinateAction_laws S Y a e ha1 hamul h).1
  inv_hom_id := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul h).2]
    have hz : (fun i => v i + -v (σ (σ.symm i))) = 0 := by
      funext i
      simp only [Equiv.apply_symm_apply, add_neg_cancel, Pi.zero_apply]
    rw [hz, mul_inv_cancel]
    exact (s2_coordinateAction_laws S Y a e ha1 hamul h).1

end HodgeLean.Foundations.Program
