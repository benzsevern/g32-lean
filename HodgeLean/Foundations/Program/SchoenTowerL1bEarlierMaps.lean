import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.Fin.Basic

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- A finite tower has compatible maps from its final object to every earlier object. -/
theorem s2v_l1b_earlier_maps {C : Type*} [Category C] (n : ℕ)
    (B : Fin (n + 1) → C) (b : ∀ j : Fin n, B j.succ ⟶ B j.castSucc) :
    ∃ c : ∀ j, B (Fin.last n) ⟶ B j,
      c (Fin.last n) = 𝟙 _ ∧ ∀ j : Fin n, c j.succ ≫ b j = c j.castSucc := by
  induction n with
  | zero =>
    refine ⟨fun j => eqToHom (congrArg B (show Fin.last 0 = j by apply Fin.ext; omega)), ?_, ?_⟩
    · simp only [eqToHom_refl]
    · intro j; exact Fin.elim0 j
  | succ n ih =>
    obtain ⟨c, hc, hb⟩ := ih (fun j => B j.castSucc) (fun j => b j.castSucc)
    let c' : ∀ j, B (Fin.last (n + 1)) ⟶ B j :=
      Fin.lastCases (𝟙 _) (fun j => b (Fin.last n) ≫ c j)
    refine ⟨c', ?_, ?_⟩
    · simp only [c', Fin.lastCases_last]
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [c', Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc,
          Category.id_comp, hc, Category.comp_id]
      · simpa only [c', Fin.succ_castSucc, Fin.lastCases_castSucc, Category.assoc]
          using congrArg (fun f => b (Fin.last n) ≫ f) (hb k)

/-- The earlier maps at a selected tower stage use the retained arrows at their original indices. -/
theorem s2v_l1b_selected_earlier_maps {C : Type*} [Category C] {r : ℕ}
    (B : Fin (r + 1) → C) (b : ∀ j : Fin r, B j.succ ⟶ B j.castSucc)
    (i : Fin r) :
    ∃ c : ∀ j : Fin (i.val + 1), B i.castSucc ⟶ B ⟨j.val, by omega⟩,
      c (Fin.last i.val) = 𝟙 (B i.castSucc) ∧
      ∀ j : Fin i.val, c j.succ ≫ b ⟨j.val, by omega⟩ = c j.castSucc := by
  exact s2v_l1b_earlier_maps i.val (fun j => B ⟨j.val, by omega⟩)
    (fun j => b ⟨j.val, by omega⟩)

/-- Compatible generic parametrizations commute with every map to an earlier base. -/
theorem s2v_l1b_earlier_maps_generic {C : Type*} [Category C] {n : ℕ}
    (B : Fin (n + 1) → C) (b : ∀ j : Fin n, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last n) ⟶ B j)
    (hc : c (Fin.last n) = 𝟙 _)
    (hb : ∀ j : Fin n, c j.succ ≫ b j = c j.castSucc)
    (T : C) (η : ∀ j, T ⟶ B j)
    (hη : ∀ j : Fin n, η j.succ ≫ b j = η j.castSucc) :
    ∀ j, η (Fin.last n) ≫ c j = η j := by
  apply Fin.reverseInduction
  · rw [hc, Category.comp_id]
  · intro j ih
    rw [← hb j, ← Category.assoc, ih, hη j]

end HodgeLean.Foundations.Program
