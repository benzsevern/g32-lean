import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFullAction
import HodgeLean.Foundations.Program.SchoenTowerI1aCategoricalOrbits
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.Program.SchoenPowerComplexPoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The coordinate translations disappear under the actual coordinatewise curve quotient. -/
theorem s2v_l1b_full_action_powerMap
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p) (n : ℕ)
    (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)) :
    s2_action S Y a e n v τ ≫ s2_powerMap p n =
      s2_powerMap p n ≫ s2_permute Z n τ := by
  apply s2_product_hom_ext n
  intro j
  simp only [Category.assoc, s2_powerMap, s2_permute, s2_action, s2_check_lift_proj]
  rw [← Category.assoc, s2_check_lift_proj, Category.assoc, hp]

/-- The composite of the actual coordinatewise curve quotient and symmetric
quotient has exactly the full coordinate-action orbits on complex points. -/
theorem s2v_l1b_full_coordinate_point_orbits
    (S : g32p_Supplier) (Y Z B : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (n : ℕ) [IsProjective (g3_power Z n).hom]
    (γ : g3_power Z n ⟶ B)
    (hγinv : ∀ τ, s2_permute Z n τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ τ, s2_permute Z n τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f) :
    ∀ x y : ComplexPoint (g3_power Y n),
      Point.map (s2_powerMap p n ≫ γ) x = Point.map (s2_powerMap p n ≫ γ) y ↔
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          Point.map (s2_action S Y a e n v τ) x = y := by
  intro x y
  constructor
  · intro hxy
    have hxy' : Point.map γ (Point.map (s2_powerMap p n) x) =
        Point.map γ (Point.map (s2_powerMap p n) y) := by
      simpa only [Point.map, Category.assoc] using hxy
    obtain ⟨τ, hτ⟩ := (s2v_i1ahi_projective_categorical_orbits
      (g3_power Z n) B (Equiv.Perm (Fin n)) (s2_permute Z n)
      (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
      γ hγinv hγ _ _).mp hxy'
    have hc (j : Fin n) :
        Point.map p (s2_powerComplexPointEquiv Y n x (τ.symm j)) =
          Point.map p (s2_powerComplexPointEquiv Y n y j) := by
      have he := congrArg (fun t => s2_powerComplexPointEquiv Z n t j) hτ
      simpa only [s2_powerComplexPointEquiv_permute, s2_powerComplexPointEquiv_powerMap] using he
    choose u hu using fun j => (hporbit _ _).mp (hc j)
    let v : Fin n → ZMod S.m := fun j => (e (u j)).toAdd
    refine ⟨v, τ, ?_⟩
    apply (s2_powerComplexPointEquiv Y n).injective
    funext j
    rw [s2_powerComplexPointEquiv_action]
    simpa only [v, ofAdd_toAdd, e.symm_apply_apply] using hu j
  · rintro ⟨v, τ, hvt⟩
    rw [← hvt]
    change x ≫ (s2_powerMap p n ≫ γ) =
      (x ≫ s2_action S Y a e n v τ) ≫ (s2_powerMap p n ≫ γ)
    rw [Category.assoc, ← Category.assoc (s2_action S Y a e n v τ),
      s2v_l1b_full_action_powerMap S Y Z a e p hp n v τ, Category.assoc, hγinv]

end HodgeLean.Foundations.Program
