import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) {W : Over (Spec ↧ℂ)} (q : g3_power Y n ⟶ W)
    (hqinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)

include hqinv hq

/-- The arbitrary-target quotient property detects equality after the retained projection. -/
theorem g32w_quotient_hom_ext {T : Over (Spec ↧ℂ)} (f g : W ⟶ T)
    (hfg : q ≫ f = q ≫ g) : f = g := by
  have hi : ∀ v τ, ∑ i, v i = 0 → s2_action S Y a e n v τ ≫ (q ≫ f) = q ≫ f := by
    intro v τ hv
    rw [← Category.assoc, hqinv v τ hv]
  obtain ⟨u, _, hu⟩ := hq T (q ≫ f) hi
  exact (hu f rfl).trans (hu g hfg.symm).symm

include ha1 hamul

/-- Every coordinate translation descends through the same zero-sum quotient. -/
theorem g32w_translation_descends (w : Fin n → ZMod S.m) :
    ∃! d : W ⟶ W, q ≫ d = s2_action S Y a e n w 1 ≫ q := by
  apply hq
  intro v τ hv
  let z : Fin n → ZMod S.m := fun i => w i + v i - w (τ.symm i)
  have hz : ∑ i, z i = 0 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp, hv,
      add_zero, sub_self]
  have hc : s2_action S Y a e n v τ ≫ s2_action S Y a e n w 1 =
      s2_action S Y a e n w 1 ≫ s2_action S Y a e n z τ := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul n).2,
      (s2_coordinateAction_laws S Y a e ha1 hamul n).2]
    simp only [one_mul, mul_one, Equiv.Perm.one_symm, Equiv.Perm.one_apply]
    congr 1
    funext i
    dsimp [z]
    abel
  rw [← Category.assoc, hc, Category.assoc, hqinv z τ hz]

end HodgeLean.Foundations.Program
