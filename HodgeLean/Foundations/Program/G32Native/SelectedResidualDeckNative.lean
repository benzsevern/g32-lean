import HodgeLean.Foundations.Program.G32Native.SelectedResidualDeck

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

include ha1 hamul

/-- Powers of a descended translation retain the coordinate square. -/
theorem g32w_translation_power (w : Fin n → ZMod S.m) (d : W ⟶ W)
    (hd : q ≫ d = s2_action S Y a e n w 1 ≫ q) (k : ℕ) :
    q ≫ (End.of d ^ k).asHom = s2_action S Y a e n (k • w) 1 ≫ q := by
  induction k with
  | zero =>
    simpa only [pow_zero, End.one_asHom, zero_nsmul, Category.comp_id,
      (s2_coordinateAction_laws S Y a e ha1 hamul n).1, Category.id_comp]
  | succ k ih =>
    rw [pow_succ']
    change q ≫ ((End.of d ^ k).asHom ≫ d) = _
    rw [← Category.assoc, ih, Category.assoc, hd, ← Category.assoc,
      (s2_coordinateAction_laws S Y a e ha1 hamul n).2]
    congr 2
    simp only [one_mul, Equiv.Perm.one_symm, Equiv.Perm.one_apply, succ_nsmul,
      Pi.add_apply, Pi.smul_apply]
    funext i
    exact add_comm _ _

include hqinv hq

/-- A descended coordinate translation has order dividing the retained modulus. -/
theorem g32w_translation_order (w : Fin n → ZMod S.m) (d : W ⟶ W)
    (hd : q ≫ d = s2_action S Y a e n w 1 ≫ q) :
    (End.of d ^ S.m).asHom = 𝟙 W := by
  apply g32w_quotient_hom_ext S Y a e n q hqinv hq
  rw [g32w_translation_power S Y a e ha1 hamul n q w d hd]
  have hz : S.m • w = 0 := by
    funext i
    change S.m • w i = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero (ZMod S.m) S.m, zero_mul]
  rw [hz, (s2_coordinateAction_laws S Y a e ha1 hamul n).1,
    Category.id_comp, Category.comp_id]

/-- The selected first-coordinate generator descends over the retained cover map. -/
theorem g32w_selectedResidualDeck
    {Z B : Over (Spec ↧ℂ)} (p₀ : Y ⟶ Z)
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (γ : g3_power Z n ⟶ B) (β₀ : W ⟶ B)
    (hβ₀ : q ≫ β₀ = s2_powerMap p₀ n ≫ γ) (hh : 0 < n) :
    ∃ d₀ : W ⟶ W, d₀ ≫ β₀ = β₀ ∧
      q ≫ d₀ = s2_action S Y a e n (s2_delta S n hh 1) 1 ≫ q ∧
      (End.of d₀ ^ S.m).asHom = 𝟙 W := by
  obtain ⟨d, hd, _⟩ := g32w_translation_descends S Y a e ha1 hamul n q hqinv hq
    (s2_delta S n hh 1)
  refine ⟨d, ?_, hd, g32w_translation_order S Y a e ha1 hamul n q hqinv hq _ d hd⟩
  apply g32w_quotient_hom_ext S Y a e n q hqinv hq
  rw [← Category.assoc, hd, Category.assoc, hβ₀, ← Category.assoc]
  suffices hs : s2_action S Y a e n (s2_delta S n hh 1) 1 ≫ s2_powerMap p₀ n =
      s2_powerMap p₀ n by rw [hs]
  apply s2_product_hom_ext n
  intro i
  simp only [s2_powerMap, Category.assoc, s2_check_lift_proj]
  rw [← Category.assoc]
  simp only [s2_action, s2_check_lift_proj, Equiv.Perm.one_symm,
    Equiv.Perm.one_apply, Category.assoc, hp₀]

end HodgeLean.Foundations.Program
