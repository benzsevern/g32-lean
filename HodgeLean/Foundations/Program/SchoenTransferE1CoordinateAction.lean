import HodgeLean.Foundations.Program.SchoenTransferE1Defs

/-! Coordinate identities for the actual deck maps of the curve powers. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- Maps into the recursive power are determined by their coordinate projections.
Source: Mathlib `CartesianMonoidalCategory.hom_ext`, the universal property of products. -/
theorem s4_e1_power_hom_ext {Y T : Over (Spec ↧ℂ)} (h : ℕ)
    (u v : T ⟶ g3_power Y h)
    (hp : ∀ i, u ≫ g3_proj Y h i = v ≫ g3_proj Y h i) : u = v := by
  induction h with
  | zero => exact (isTerminalTensorUnit (C := Over (Spec ↧ℂ))).hom_ext u v
  | succ h ih =>
      apply CartesianMonoidalCategory.hom_ext
      · exact hp 0
      · apply ih
        intro i
        have hi := hp i.succ
        change u ≫ (snd Y (g3_power Y h) ≫ g3_proj Y h i) =
          v ≫ (snd Y (g3_power Y h) ≫ g3_proj Y h i) at hi
        exact (Category.assoc u (snd Y (g3_power Y h)) (g3_proj Y h i)).trans
          (hi.trans (Category.assoc v (snd Y (g3_power Y h)) (g3_proj Y h i)).symm)

/-- The recursive lift has the prescribed coordinates.
Source: Mathlib `CartesianMonoidalCategory.lift_fst` and `lift_snd`. -/
theorem s4_e1_power_lift_projection {Y T : Over (Spec ↧ℂ)} (h : ℕ)
    (f : Fin h → (T ⟶ Y)) (i : Fin h) :
    s2_lift h f ≫ g3_proj Y h i = f i := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact CartesianMonoidalCategory.lift_fst _ _
      · change CartesianMonoidalCategory.lift _ _ ≫
          (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y h j) = _
        rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
        exact ih _ j

/-- The actual deck-permutation map has its specified coordinate square.
Source: Schoen (1988), §1, p. 5, and §2, p. 12. -/
theorem s4_e1_action_projection
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (h : ℕ) (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)) (i : Fin h) :
    s2_action S Y a e h v σ ≫ g3_proj Y h i =
      g3_proj Y h (σ.symm i) ≫ a (e.symm (.ofAdd (v i))) :=
  s4_e1_power_lift_projection h _ i

/-- The zero deck tuple gives the identity on the actual scheme power.
Source: Schoen (1988), §1, p. 5, the deck group action. -/
theorem s4_e1_deck_action_zero
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (h : ℕ) :
    s2_action S Y a e h 0 1 = 𝟙 (g3_power Y h) := by
  apply s4_e1_power_hom_ext
  intro i
  have he := s4_e1_action_projection S Y a e h 0 1 i
  change s2_action S Y a e h 0 1 ≫ g3_proj Y h i =
    g3_proj Y h i ≫ a (e.symm (.ofAdd 0)) at he
  rw [ofAdd_zero, map_one, ha1, Category.comp_id] at he
  exact he.trans (Category.id_comp (g3_proj Y h i)).symm

/-- Actual coordinate deck maps compose by addition of their tuples.
Source: Schoen (1988), §1, p. 5, the deck group action. -/
theorem s4_e1_deck_action_add
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h : ℕ) (v w : Fin h → ZMod S.m) :
    s2_action S Y a e h v 1 ≫ s2_action S Y a e h w 1 =
      s2_action S Y a e h (v + w) 1 := by
  apply s4_e1_power_hom_ext
  intro i
  have hv := s4_e1_action_projection S Y a e h v 1 i
  have hw := s4_e1_action_projection S Y a e h w 1 i
  have ht := s4_e1_action_projection S Y a e h (v + w) 1 i
  change s2_action S Y a e h v 1 ≫ g3_proj Y h i =
    g3_proj Y h i ≫ a (e.symm (.ofAdd (v i))) at hv
  change s2_action S Y a e h w 1 ≫ g3_proj Y h i =
    g3_proj Y h i ≫ a (e.symm (.ofAdd (w i))) at hw
  change s2_action S Y a e h (v + w) 1 ≫ g3_proj Y h i =
    g3_proj Y h i ≫ a (e.symm (.ofAdd (v i + w i))) at ht
  calc
    (s2_action S Y a e h v 1 ≫ s2_action S Y a e h w 1) ≫ g3_proj Y h i =
        (s2_action S Y a e h v 1 ≫ g3_proj Y h i) ≫ a (e.symm (.ofAdd (w i))) := by
          rw [Category.assoc, hw, ← Category.assoc]
    _ = (g3_proj Y h i ≫ a (e.symm (.ofAdd (v i)))) ≫ a (e.symm (.ofAdd (w i))) := by rw [hv]
    _ = g3_proj Y h i ≫ a (e.symm (.ofAdd (v i + w i))) := by
      rw [Category.assoc, ← hamul, ← map_mul]
      rfl
    _ = s2_action S Y a e h (v + w) 1 ≫ g3_proj Y h i := ht.symm

#print axioms s4_e1_power_hom_ext
#print axioms s4_e1_power_lift_projection
#print axioms s4_e1_action_projection
#print axioms s4_e1_deck_action_zero
#print axioms s4_e1_deck_action_add
end HodgeLean.Foundations.Program
