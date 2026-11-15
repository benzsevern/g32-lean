import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackProducts
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite sequence of weighted transform identities retains every exceptional factor. -/
theorem s2v_l1b_fin_weighted_transform_recurrence
    {R : Type*} [CommMonoid R] (n m : ℕ)
    (D : Fin (n + 1) → R) (E : Fin n → R)
    (hstep : ∀ j, D j.castSucc = D j.succ * E j ^ m) :
    D 0 = D (Fin.last n) * (∏ j, E j) ^ m := by
  induction n with
  | zero => simp only [Fin.last_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_pow, mul_one]
  | succ n ih =>
    have htail := ih (fun j => D j.succ) (fun j => E j.succ)
      (fun j => hstep j.succ)
    have hhead := hstep (0 : Fin (n + 1))
    rw [Fin.castSucc_zero] at hhead
    rw [hhead, htail, Fin.prod_univ_succ, mul_pow]
    ac_rfl

/-- One-step ideal identities telescope along the actual composites, retaining every earlier centre total pullback. -/
theorem s2v_l1b_weighted_tower_total_transform
    (n m : ℕ) (B : Fin (n + 1) → Scheme)
    (b : ∀ j : Fin n, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last n) ⟶ B j)
    (hc : c (Fin.last n) = 𝟙 _)
    (hb : ∀ j : Fin n, c j.succ ≫ b j = c j.castSucc)
    (P : ∀ j, (B j).IdealSheafData)
    (E : ∀ j : Fin n, (B j.castSucc).IdealSheafData)
    (hstep : ∀ j : Fin n, (P j.castSucc).comap (b j) =
      P j.succ * ((E j).comap (b j)) ^ m) :
    (P 0).comap (c 0) = P (Fin.last n) *
      (∏ j : Fin n, (E j).comap (c j.castSucc)) ^ m := by
  have hstep' (j : Fin n) :
      (P j.castSucc).comap (c j.castSucc) =
        (P j.succ).comap (c j.succ) * ((E j).comap (c j.castSucc)) ^ m := by
    have H := congrArg (fun I => I.comap (c j.succ)) (hstep j)
    rw [s2v_l1b_comap_mul, s2v_l1b_comap_pow,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      hb j] at H
    exact H
  have H := s2v_l1b_fin_weighted_transform_recurrence n m
    (fun j => (P j).comap (c j))
    (fun j : Fin n => (E j).comap (c j.castSucc)) hstep'
  simpa only [hc, Scheme.IdealSheafData.comap_id] using H

end HodgeLean.Foundations.Program
