import HodgeLean.Papers.SkeletonG34FiniteDefs

set_option maxHeartbeats 200000

noncomputable section
open CategoryTheory
namespace HodgeLean.Papers

/-- Descent modulo three for the norm form in Example 12.2.
Source: G34 v1.5, Example 12.2; elementary integer descent. -/
theorem skelg34_norm_descent (k : ℤ) (hk : (k : ZMod 3) = 2) :
    ∀ (n : ℕ) (p q : ℤ), p ^ 2 + 3 * q ^ 2 = k * (n : ℤ) ^ 2 → n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hpq
    by_contra hn
    have key : ∀ x y z : ZMod 3, x ^ 2 + 3 * z ^ 2 = 2 * y ^ 2 →
        x = 0 ∧ y = 0 := by decide
    have hmod := congrArg (Int.cast : ℤ → ZMod 3) hpq
    push_cast at hmod
    rw [hk] at hmod
    obtain ⟨hp3, hn3⟩ := key _ _ _ hmod
    obtain ⟨p', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd p 3).1 hp3
    obtain ⟨n', rfl⟩ := (ZMod.natCast_eq_zero_iff n 3).1 hn3
    have hq : (3 : ℤ) ∣ q ^ 2 :=
      ⟨k * (n' : ℤ) ^ 2 - p' ^ 2, by push_cast at hpq; nlinarith [hpq]⟩
    obtain ⟨q', rfl⟩ := Int.prime_three.dvd_of_dvd_pow hq
    have h' : p' ^ 2 + 3 * q' ^ 2 = k * (n' : ℤ) ^ 2 := by
      push_cast at hpq
      nlinarith [hpq]
    have := ih n' (by omega) p' q' h'
    omega

/-- Integers congruent to two modulo three are not rational norms of this form.
Source: G34 v1.5, Example 12.2; elementary integer descent. -/
theorem skelg34_not_norm (k : ℤ) (hk : (k : ZMod 3) = 2) (x y : ℚ) :
    x ^ 2 + 3 * y ^ 2 ≠ k := by
  intro hxy
  have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have hy : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
  have hint : (x.num * y.den) ^ 2 + 3 * (y.num * x.den) ^ 2 =
      k * ((x.den * y.den : ℕ) : ℤ) ^ 2 := by
    have : ((x.num * y.den : ℤ) : ℚ) ^ 2 + 3 * ((y.num * x.den : ℤ) : ℚ) ^ 2 =
        k * ((x.den * y.den : ℕ) : ℚ) ^ 2 := by
      push_cast
      rw [hx, hy]
      linear_combination ((x.den : ℚ) * y.den) ^ 2 * hxy
    exact_mod_cast this
  have := skelg34_norm_descent k hk _ _ _ hint
  simp [x.den_nz, y.den_nz] at this

/-- The two explicit nonsplit norm classes from the type-III example.
The quaternionic varieties and polarization realization are not asserted here.
Source: G34 v1.5, Example 12.2. -/
theorem skelg34_typeIII_classes_aux :
    skelg34_pureNorm (-3) (-1) 0 1 0 = 1 ∧
    skelg34_pureNorm (-3) (-1) 1 0 0 = 3 ∧
    skelg34_pureNorm (-3) (-1) 1 0 2 = 15 ∧
    skelg34_pureNorm (-3) (-1) 1 4 1 = 22 ∧
    skelg34_pureNorm (-3) (-1) 1 0 1 = 6 ∧
    (1 * 3 * 15 : ℚ) = 45 ∧ (22 * 3 * 6 : ℚ) = 396 ∧
    SameNormClass 3 (-45) (-5) ∧ SameNormClass 3 (-396) (-11) ∧
    ¬ SameNormClass 3 (-5) (-1) ∧ ¬ SameNormClass 3 (-11) (-1) := by
  refine ⟨by norm_num [skelg34_pureNorm], by norm_num [skelg34_pureNorm],
    by norm_num [skelg34_pureNorm], by norm_num [skelg34_pureNorm],
    by norm_num [skelg34_pureNorm], by norm_num, by norm_num,
    ⟨3, 0, by norm_num, by norm_num⟩, ⟨6, 0, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rintro ⟨x, y, _, h⟩
    exact skelg34_not_norm 5 (by decide) x y (by norm_num; linarith)
  · rintro ⟨x, y, _, h⟩
    exact skelg34_not_norm 11 (by decide) x y (by norm_num; linarith)

/-- The determinant formula and division by the quadratic generator in the printed basis.
This is a matrix identity, without a quaternionic polarization-realization assertion.
Source: G34 v1.5, Example 12.2. -/
theorem skelg34_typeIII_determinant_aux (a b α β γ : ℚ) (u : ℂ) (hu : u^2 = (a : ℂ)) :
    (skelg34_typeIIIGram b α β γ u).det = (-b * skelg34_pureNorm a b α β γ : ℚ) ∧
    (u⁻¹ • skelg34_typeIIIGram b α β γ u).det =
      ((-b * skelg34_pureNorm a b α β γ / a : ℚ) : ℂ) := by
  have hdet : (skelg34_typeIIIGram b α β γ u).det =
      ((-b * skelg34_pureNorm a b α β γ : ℚ) : ℂ) := by
    rw [Matrix.det_fin_two]
    change (α : ℂ)*u*((α : ℂ)*b*u) -
      ((b : ℂ)*(β + γ*u))*(-(b : ℂ)*(β - γ*u)) = _
    simp only [skelg34_pureNorm]
    push_cast
    linear_combination ((α : ℂ)^2 * b - (b : ℂ)^2 * γ^2) * hu
  refine ⟨hdet, ?_⟩
  rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hu, hdet]
  push_cast
  ring

end HodgeLean.Papers
