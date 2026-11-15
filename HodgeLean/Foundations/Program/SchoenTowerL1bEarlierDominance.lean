import HodgeLean.Foundations.Program.SchoenTowerL1bEarlierMaps
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible maps to the initial base are dominant when the retained initial parametrization is. -/
theorem s2v_l1b_selected_earlier_maps_dominant
    {S₀ : Scheme} {r : ℕ} (B : Fin (r + 1) → Over S₀)
    (b : ∀ j : Fin r, B j.succ ⟶ B j.castSucc) (i : Fin r)
    (c : ∀ j : Fin (i.val + 1), B i.castSucc ⟶ B ⟨j.val, by omega⟩)
    (hc : c (Fin.last i.val) = 𝟙 (B i.castSucc))
    (hb : ∀ j : Fin i.val, c j.succ ≫ b ⟨j.val, by omega⟩ = c j.castSucc)
    (T : Scheme) (η : ∀ j, T ⟶ (B j).left) [hηdom : IsDominant (η 0)]
    (hη : ∀ j : Fin r, η j.succ ≫ (b j).left = η j.castSucc) :
    IsDominant (c 0).left := by
  have H : η i.castSucc ≫ (c 0).left = η 0 :=
    s2v_l1b_earlier_maps_generic
      (fun j : Fin (i.val + 1) => (B ⟨j.val, by omega⟩).left)
      (fun j => (b ⟨j.val, by omega⟩).left) (fun j => (c j).left)
      (congrArg Over.Hom.left hc) (fun j => congrArg Over.Hom.left (hb j))
      T (fun j => η ⟨j.val, by omega⟩) (fun j => hη ⟨j.val, by omega⟩) 0
  haveI : IsDominant (η i.castSucc ≫ (c 0).left) := by
    rw [H]
    exact hηdom
  exact IsDominant.of_comp (η i.castSucc) (c 0).left

end HodgeLean.Foundations.Program
