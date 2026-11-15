import HodgeLean.Foundations.Program.SchoenTowerL1bTowerFactorization
import HodgeLean.Foundations.Program.SchoenTowerL1bChartFactorization
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFactorization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Weighted one-step identities give the section equation with every earlier centre factor. -/
theorem s2v_l1b_tower_section_factorization
    (k m : ℕ) (B : Fin (k + 1) → Scheme)
    [IsIntegral (B (Fin.last k))]
    (b : ∀ j : Fin k, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last k) ⟶ B j)
    (hc : c (Fin.last k) = 𝟙 _)
    (hb : ∀ j : Fin k, c j.succ ≫ b j = c j.castSucc)
    {J : Type*} [Fintype J] [DecidableEq J]
    (D : ∀ j, J → (B j).IdealSheafData)
    (E : ∀ j : Fin k, (B j.castSucc).IdealSheafData)
    (n : J → ℕ)
    (hstep : ∀ j : Fin k,
      (∏ t, ((D j.castSucc t).comap (b j)) ^ n t) =
        (∏ t, D j.succ t ^ n t) * ((E j).comap (b j)) ^ m)
    (U : (B (Fin.last k)).affineOpens) [Nonempty U.1]
    (g : J → Γ(B (Fin.last k), U)) (eE : Fin k → Γ(B (Fin.last k), U))
    (a d : J) (had : a ≠ d) (hn : n a + n d = m)
    (u v : Γ(B (Fin.last k), U))
    (hg : ∀ t, ((D 0 t).comap (c 0)).ideal U = Ideal.span {g t})
    (hE : ∀ j, ((E j).comap (c j.castSucc)).ideal U = Ideal.span {eE j})
    (hu : (D (Fin.last k) a).ideal U = Ideal.span {u})
    (hv : (D (Fin.last k) d).ideal U = Ideal.span {v})
    (hrest : ∀ t, t ≠ a → t ≠ d → (D (Fin.last k) t).ideal U = ⊤) :
    ∃ δ : Γ(B (Fin.last k), U)ˣ,
      (∏ t, g t ^ n t) = (δ : Γ(B (Fin.last k), U)) *
        u ^ n a * v ^ (m - n a) * (∏ j, eE j) ^ m := by
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
    Pi.pow_apply, hg, hE] at H'
  have htwo := s2v_l1b_weighted_product_two_factors
    (fun t => (D (Fin.last k) t).ideal U) n a d had
    (fun t hta htd => by simpa only [Ideal.one_eq_top] using hrest t hta htd)
  rw [htwo, hu, hv] at H'
  have hd : n d = m - n a := by omega
  rw [hd] at H'
  exact s2v_l1b_unit_of_weighted_ideal_identity g n eE u v m (n a) H'

end HodgeLean.Foundations.Program
