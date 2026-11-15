import HodgeLean.Foundations.Program.SchoenTowerDefs

/-! # Total maps for finite towers
The construction uses only the supplied transitions and initial map.
-/

noncomputable section
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Compose successive tower maps to the retained initial target. -/
def s2e_towerTotalMap {C : Type*} [Category C] {r : ℕ}
    (W : Fin (r + 1) → C) {W₀ : C} (e₀ : W 0 ⟶ W₀)
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc) : ∀ i, W i ⟶ W₀ :=
  Fin.induction e₀ (fun i f => w i ≫ f)

@[simp] theorem s2e_towerTotalMap_zero {C : Type*} [Category C] {r : ℕ}
    (W : Fin (r + 1) → C) {W₀ : C} (e₀ : W 0 ⟶ W₀)
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc) :
    s2e_towerTotalMap W e₀ w 0 = e₀ := rfl

@[simp] theorem s2e_towerTotalMap_succ {C : Type*} [Category C] {r : ℕ}
    (W : Fin (r + 1) → C) {W₀ : C} (e₀ : W 0 ⟶ W₀)
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc) (i : Fin r) :
    s2e_towerTotalMap W e₀ w i.succ = w i ≫ s2e_towerTotalMap W e₀ w i.castSucc := by
  exact Fin.induction_succ _ _ i

/-- Equivariance of transitions propagates to the total map. -/
theorem s2e_towerTotalMap_equivariant {C : Type*} [Category C] {r : ℕ}
    (W : Fin (r + 1) → C) {W₀ : C} (e₀ : W 0 ⟶ W₀)
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (d : ∀ i, W i ⟶ W i) (d₀ : W₀ ⟶ W₀)
    (h₀ : d 0 ≫ e₀ = e₀ ≫ d₀)
    (hw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (i : Fin (r + 1)) :
    d i ≫ s2e_towerTotalMap W e₀ w i = s2e_towerTotalMap W e₀ w i ≫ d₀ := by
  induction i using Fin.induction with
  | zero => exact h₀
  | succ i ih =>
    rw [s2e_towerTotalMap_succ, ← Category.assoc, hw i, Category.assoc,
      ih, Category.assoc]

/-- The transition equations uniquely specify all maps to the initial target. -/
theorem s2e_towerTotalMap_unique {C : Type*} [Category C] {r : ℕ}
    (W : Fin (r + 1) → C) {W₀ : C} (e₀ : W 0 ⟶ W₀)
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (f : ∀ i, W i ⟶ W₀) (h₀ : f 0 = e₀)
    (hf : ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc)
    (i : Fin (r + 1)) : f i = s2e_towerTotalMap W e₀ w i := by
  induction i using Fin.induction with
  | zero => exact h₀
  | succ i ih => rw [hf, s2e_towerTotalMap_succ, ih]

end HodgeLean.Foundations.Program
