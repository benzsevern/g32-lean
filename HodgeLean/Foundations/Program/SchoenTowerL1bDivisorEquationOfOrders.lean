import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorWeightedOrders

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Weighted prime-order congruences give the exact equation with rational corrections. -/
theorem s2v_l1b_divisor_equation_of_orders
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (ρ : R →+* K) (hρ : Function.Injective ρ)
    {J : Type*} [Fintype J] (g : J → R) (n : J → ℕ) (hg : ∀ j, g j ≠ 0)
    (m : ℕ) (hm : 0 < m) (t : K)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ^ m = ρ a / ρ b)
    (hv : ∀ p : R, Prime p → Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ))) :
    ∃ (ε : Rˣ) (A B : R), A ≠ 0 ∧ B ≠ 0 ∧
      t ^ m * (ρ B) ^ m = ρ (ε : R) * (∏ j, ρ (g j) ^ n j) * (ρ A) ^ m := by
  have hP : (∏ j, g j ^ n j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hg j)
  have hv' (p : R) (hp : Prime p) : Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      ((emultiplicity p (∏ j, g j ^ n j)).toNat : ℤ) := by
    rw [s2v_l1b_divisor_weighted_product_order g n hg p hp]
    exact hv p hp
  obtain ⟨ε, A, B, hA, hB, heq⟩ :=
    s2v_l1b_divisor_correction_of_orders a b (∏ j, g j ^ n j) ha hb hP m hm hv'
  have hbK : ρ b ≠ 0 := by simpa only [map_zero] using hρ.ne hb
  have he := congrArg ρ heq
  simp only [map_mul, map_pow, map_prod] at he
  refine ⟨ε, A, B, hA, hB, ?_⟩
  rw [ht, div_mul_eq_mul_div, div_eq_iff hbK]
  calc
    _ = ρ (ε : R) * ρ b * (∏ j, ρ (g j) ^ n j) * ρ A ^ m := he
    _ = _ := by ring

end HodgeLean.Foundations.Program
