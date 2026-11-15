import HodgeLean.Foundations.Program.SchoenTowerL1bTowerFactorization
import HodgeLean.Foundations.Program.SchoenTowerL1bChartFactorization

/-! # Weighted total branch ideals away from final strict transforms -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- If all final strict-transform ideals are units, the total weighted branch
ideal is a degree-th power of the product of earlier centre ideals. -/
theorem s2e_c1_final_weighted_ideal_power
    (k m : ℕ) (B : Fin (k + 1) → Scheme)
    (b : ∀ j : Fin k, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last k) ⟶ B j)
    (hc : c (Fin.last k) = 𝟙 _) (hb : ∀ j : Fin k, c j.succ ≫ b j = c j.castSucc)
    {J : Type*} [Fintype J]
    (D : ∀ j, J → (B j).IdealSheafData)
    (E : ∀ j : Fin k, (B j.castSucc).IdealSheafData) (n : J → ℕ)
    (hstep : ∀ j : Fin k,
      (∏ t, ((D j.castSucc t).comap (b j)) ^ n t) =
        (∏ t, D j.succ t ^ n t) * ((E j).comap (b j)) ^ m)
    (U : (B (Fin.last k)).affineOpens)
    (g : J → Γ(B (Fin.last k), U)) (eE : Fin k → Γ(B (Fin.last k), U))
    (hg : ∀ t, ((D 0 t).comap (c 0)).ideal U = Ideal.span {g t})
    (hE : ∀ j, ((E j).comap (c j.castSucc)).ideal U = Ideal.span {eE j})
    (hfinal : ∀ t, (D (Fin.last k) t).ideal U = ⊤) :
    (∏ t, (Ideal.span {g t}) ^ n t) = (Ideal.span {∏ j, eE j}) ^ m := by
  have H := s2v_l1b_weighted_tower_total_transform k m B b c hc hb
    (fun j => ∏ t, D j t ^ n t) E (fun j => by
      rw [s2v_l1b_comap_prod]
      simp_rw [s2v_l1b_comap_pow]
      exact hstep j)
  have H' := congrArg (fun I => I.ideal U) H
  rw [s2v_l1b_comap_prod] at H'
  simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_mul,
    Scheme.IdealSheafData.ideal_pow, Pi.mul_apply, Pi.pow_apply] at H'
  simp_rw [s2v_l1b_comap_pow, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply, hg, hE, hfinal] at H'
  simpa only [← Ideal.one_eq_top, one_pow, Finset.prod_const_one, one_mul,
    Ideal.prod_span_singleton] using H'

end HodgeLean.Foundations.Program
