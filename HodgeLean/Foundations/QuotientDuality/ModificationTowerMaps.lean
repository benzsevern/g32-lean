import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! Source equations and functoriality for the specified total tower map. -/
noncomputable section
open CategoryTheory HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem towerTotalMap_postcomp {C : Type*} [Category C] {r : ℕ}
    (X : Fin (r + 1) → C) {Y Z : C} (f : X 0 ⟶ Y)
    (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) (g : Y ⟶ Z)
    (i : Fin (r + 1)) :
    s2e_towerTotalMap X (f ≫ g) w i = s2e_towerTotalMap X f w i ≫ g := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, ih, Category.assoc]

theorem towerTotalMap_source {C : Type*} [Category C] {r : ℕ}
    (X : Fin (r + 1) → C) {Y T : C} (f : X 0 ⟶ Y)
    (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (a : ∀ i, T ⟶ X i) (ha : ∀ i : Fin r, a i.succ ≫ w i = a i.castSucc)
    (i : Fin (r + 1)) :
    a i ≫ s2e_towerTotalMap X f w i = a 0 ≫ f := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, ha j, ih]

theorem towerTotalMap_functor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {r : ℕ} (X : Fin (r + 1) → C) {Y : C} (f : X 0 ⟶ Y)
    (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) (i : Fin (r + 1)) :
    F.map (s2e_towerTotalMap X f w i) =
      s2e_towerTotalMap (fun j => F.obj (X j)) (F.map f) (fun j => F.map (w j)) i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, F.map_comp, ih]

#print axioms towerTotalMap_source
end HodgeLean.Foundations.QuotientDuality
