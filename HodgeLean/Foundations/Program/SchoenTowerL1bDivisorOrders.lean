import HodgeLean.Foundations.Program.SchoenTowerL1bKvalResidueTransport

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Prime orders of a finite weighted product are the weighted sum of prime orders. -/
theorem s2v_l1b_divisor_product_order
    {R J : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Fintype J] {p : R} (hp : Prime p) (g : J → R) (n : J → ℕ)
    (hg : ∀ j, g j ≠ 0) :
    ((emultiplicity p (∏ j, g j ^ n j)).toNat : ℤ) =
      ∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ) := by
  classical
  have H (s : Finset J) :
      ((emultiplicity p (∏ j ∈ s, g j ^ n j)).toNat : ℤ) =
        ∑ j ∈ s, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      rw [emultiplicity_eq_zero.mpr (fun hd => hp.not_unit (isUnit_of_dvd_one hd))]
      rfl
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        s2v_l1b_kval_prime_order_mul hp (pow_ne_zero _ (hg j))
          (Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hg k))),
        s2v_l1b_kval_prime_order_pow hp, ih]
  exact H Finset.univ

/-- A unit and rational m-th-power corrections do not change weighted prime residues. -/
theorem s2v_l1b_divisor_equation_orders
    {R K J : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Fintype J] (ρ : R →+* K) (hρ : Function.Injective ρ)
    {p a b A B : R} (hp : Prime p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (ε : Rˣ) (g : J → R) (n : J → ℕ)
    (hg : ∀ j, g j ≠ 0) (m : ℕ)
    (he : (ρ a / ρ b) * (ρ B) ^ m =
      ρ (ε : R) * (∏ j, (ρ (g j)) ^ n j) * (ρ A) ^ m) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ)) := by
  have nz (v : R) (hv : v ≠ 0) : ρ v ≠ 0 := by simpa only [map_zero] using hρ.ne hv
  have hP : (∏ j, g j ^ n j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hg j))
  have he' : ρ a / ρ b =
      ρ ((ε : R) * (∏ j, g j ^ n j) * A ^ m) / ρ (B ^ m) := by
    rw [map_pow]
    apply (eq_div_iff (pow_ne_zero m (nz B hB))).mpr
    simpa only [map_mul, map_prod, map_pow] using he
  have ho := s2v_l1b_kval_fraction_order_eq ρ hρ hp ha hb
    (mul_ne_zero (mul_ne_zero ε.ne_zero hP) (pow_ne_zero m hA))
    (pow_ne_zero m hB) he'
  rw [s2v_l1b_kval_prime_order_mul hp
      (mul_ne_zero ε.ne_zero hP) (pow_ne_zero m hA),
    s2v_l1b_kval_prime_order_mul hp ε.ne_zero hP,
    s2v_l1b_kval_prime_order_pow hp, s2v_l1b_kval_prime_order_pow hp,
    emultiplicity_eq_zero.mpr (fun hd => hp.not_unit (isUnit_of_dvd_unit hd ε.isUnit)),
    ENat.toNat_zero, Nat.cast_zero, zero_add,
    s2v_l1b_divisor_product_order hp g n hg] at ho
  rw [ho]
  apply Int.modEq_iff_dvd.mpr
  refine ⟨((emultiplicity p B).toNat : ℤ) - ((emultiplicity p A).toNat : ℤ), ?_⟩
  ring

end HodgeLean.Foundations.Program
