import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-! Arithmetic helpers for the finite-box proof of Legendre's ternary theorem. -/

namespace HodgeLean.Foundations.MeyerRational

/-- The polynomial transformation used for the second value in the finite box.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, p. 6. -/
theorem legendre_composition (a b c x y z : ℤ) :
    a * (x * z + b * y) ^ 2 + b * (y * z - a * x) ^ 2 +
      c * (z ^ 2 + a * b) ^ 2 =
      (z ^ 2 + a * b) * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + a * b * c) := by
  ring

/-- A representation of the second possible box value yields a nonzero zero.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, p. 6. -/
theorem legendre_zero_of_neg_product (a b c x y z : ℤ) (hab : 0 < a * b)
    (h : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = -(a * b * c)) :
    ∃ u v w : ℤ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      a * u ^ 2 + b * v ^ 2 + c * w ^ 2 = 0 := by
  refine ⟨x * z + b * y, y * z - a * x, z ^ 2 + a * b, ?_, ?_⟩
  · exact Or.inr (Or.inr (by nlinarith [sq_nonneg z]))
  · rw [legendre_composition, h]
    ring

/-- Only two multiples occur in the strict bounds from the box.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, p. 7. -/
theorem legendre_two_values (m t : ℤ) (hm : 0 < m) (hd : m ∣ t)
    (hl : -(2 * m) < t) (hu : t < m) : t = 0 ∨ t = -m := by
  obtain ⟨k, rfl⟩ := hd
  have hk : -2 < k ∧ k < 1 := by
    constructor <;> nlinarith
  have : k = 0 ∨ k = -1 := by omega
  rcases this with rfl | rfl <;> simp

theorem legendre_box_card (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    A * B * C < ((B * C).sqrt + 1) * ((C * A).sqrt + 1) * ((A * B).sqrt + 1) := by
  have h₁ := Nat.lt_succ_sqrt' (B * C)
  have h₂ := Nat.lt_succ_sqrt' (C * A)
  have h₃ := Nat.lt_succ_sqrt' (A * B)
  have ht : (B * C) * (C * A) * (A * B) <
      ((B * C).sqrt + 1) ^ 2 * ((C * A).sqrt + 1) ^ 2 * ((A * B).sqrt + 1) ^ 2 :=
    mul_lt_mul (mul_lt_mul h₁ h₂.le (by positivity) (by positivity))
      h₃.le (by positivity) (by positivity)
  have he : (B * C) * (C * A) * (A * B) = (A * B * C) ^ 2 := by ring
  rw [he] at ht
  have he' : ((B * C).sqrt + 1) ^ 2 * ((C * A).sqrt + 1) ^ 2 *
      ((A * B).sqrt + 1) ^ 2 =
      (((B * C).sqrt + 1) * ((C * A).sqrt + 1) * ((A * B).sqrt + 1)) ^ 2 := by ring
  rw [he'] at ht
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) ht

theorem legendre_sqrt_strict (n : ℕ) (hn : ¬IsSquare n) : n.sqrt ^ 2 < n := by
  refine lt_of_le_of_ne (Nat.sqrt_le' n) ?_
  intro he
  exact hn ⟨n.sqrt, by simpa only [sq] using he.symm⟩

theorem legendre_difference_sq (n : ℕ) (i j : Fin (n.sqrt + 1)) :
    ((i.val : ℤ) - j.val) ^ 2 ≤ (n.sqrt : ℤ) ^ 2 := by
  have hi : (i.val : ℤ) ≤ n.sqrt := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hj : (j.val : ℤ) ≤ n.sqrt := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hi₀ : (0 : ℤ) ≤ i.val := by positivity
  have hj₀ : (0 : ℤ) ≤ j.val := by positivity
  nlinarith

theorem legendre_box_kernel (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (r : ZMod A) (s : ZMod B) (t : ZMod C) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 ≤ ((B * C).sqrt : ℤ) ^ 2 ∧
      y ^ 2 ≤ ((C * A).sqrt : ℤ) ^ 2 ∧
      z ^ 2 ≤ ((A * B).sqrt : ℤ) ^ 2 ∧
      r * (y : ZMod A) + (C : ZMod A) * z = 0 ∧
      s * (z : ZMod B) - (A : ZMod B) * x = 0 ∧
      t * (x : ZMod C) - (B : ZMod C) * y = 0 := by
  let : NeZero A := ⟨by omega⟩
  let : NeZero B := ⟨by omega⟩
  let : NeZero C := ⟨by omega⟩
  let f : Fin ((B * C).sqrt + 1) × Fin ((C * A).sqrt + 1) × Fin ((A * B).sqrt + 1) →
      ZMod A × ZMod B × ZMod C := fun v =>
    (r * v.2.1.val + C * v.2.2.val,
     s * v.2.2.val - A * v.1.val,
     t * v.1.val - B * v.2.1.val)
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card, mul_assoc] using
      legendre_box_card A B C hA hB hC)
  refine ⟨(u.1.val : ℤ) - v.1.val, (u.2.1.val : ℤ) - v.2.1.val,
    (u.2.2.val : ℤ) - v.2.2.val, ?_, legendre_difference_sq _ _ _,
    legendre_difference_sq _ _ _, legendre_difference_sq _ _ _, ?_, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    apply huv
    apply Prod.ext
    · apply Fin.ext
      exact_mod_cast sub_eq_zero.mp hn.1
    · apply Prod.ext <;> apply Fin.ext
      · exact_mod_cast sub_eq_zero.mp hn.2.1
      · exact_mod_cast sub_eq_zero.mp hn.2.2
  · have h := congrArg Prod.fst he
    dsimp [f] at h
    push_cast
    linear_combination h
  · have h := congrArg (fun w => w.2.1) he
    dsimp [f] at h
    push_cast
    linear_combination h
  · have h := congrArg (fun w => w.2.2) he
    dsimp [f] at h
    push_cast
    linear_combination h

theorem legendre_residue_factor {R : Type*} [CommRing R] (b c r y z : R)
    (hc : IsUnit c) (hr : r ^ 2 = -(b * c)) (hl : r * y + c * z = 0) :
    b * y ^ 2 + c * z ^ 2 = 0 := by
  apply hc.mul_left_cancel
  linear_combination y ^ 2 * hr + (c * z - r * y) * hl

theorem legendre_box_divisible (A B C : ℕ)
    (hAB : A.Coprime B) (hBC : B.Coprime C) (hCA : C.Coprime A)
    (r : ZMod A) (s : ZMod B) (t : ZMod C)
    (hr : r ^ 2 = (B : ZMod A) * C) (hs : s ^ 2 = (C : ZMod B) * A)
    (ht : t ^ 2 = -((A : ZMod C) * B))
    (x y z : ℤ)
    (h₁ : r * (y : ZMod A) + (C : ZMod A) * z = 0)
    (h₂ : s * (z : ZMod B) - (A : ZMod B) * x = 0)
    (h₃ : t * (x : ZMod C) - (B : ZMod C) * y = 0) :
    (A * B * C : ℤ) ∣ -(A : ℤ) * x ^ 2 - (B : ℤ) * y ^ 2 + (C : ℤ) * z ^ 2 := by
  apply (hCA.symm.isCoprime.mul_left hBC.isCoprime).mul_dvd
  · apply hAB.isCoprime.mul_dvd
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ A).mp
      push_cast
      simp only [ZMod.natCast_self, neg_zero, zero_mul, zero_sub]
      have h := legendre_residue_factor (-(B : ZMod A)) C r y z
        ((ZMod.isUnit_iff_coprime C A).mpr hCA) (by simpa using hr) h₁
      simpa [sub_eq_add_neg] using h
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ B).mp
      push_cast
      simp only [ZMod.natCast_self, zero_mul, sub_zero]
      have h := legendre_residue_factor (C : ZMod B) (-A) s z x
        (((ZMod.isUnit_iff_coprime A B).mpr hAB).neg) (by simpa using hs)
        (by simpa [sub_eq_add_neg] using h₂)
      linear_combination h
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ C).mp
    push_cast
    simp only [ZMod.natCast_self, zero_mul, add_zero]
    have h := legendre_residue_factor (-(A : ZMod C)) (-B) t x y
      (((ZMod.isUnit_iff_coprime B C).mpr hBC).neg) (by simpa using ht)
      (by simpa [sub_eq_add_neg] using h₃)
    simpa [sub_eq_add_neg] using h

/-- The finite-box argument when the three pairwise products are nonsquares.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, pp. 6–7. -/
theorem legendre_of_nonsquare_products (A B C : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : A.Coprime B) (hBC : B.Coprime C) (hCA : C.Coprime A)
    (nAB : ¬IsSquare (A * B)) (nBC : ¬IsSquare (B * C)) (nCA : ¬IsSquare (C * A))
    (rA : IsSquare ((B : ZMod A) * C))
    (rB : IsSquare ((C : ZMod B) * A))
    (rC : IsSquare (-((A : ZMod C) * B))) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      -(A : ℤ) * x ^ 2 - (B : ℤ) * y ^ 2 + (C : ℤ) * z ^ 2 = 0 := by
  obtain ⟨r, hr⟩ := rA
  obtain ⟨s, hs⟩ := rB
  obtain ⟨t, ht⟩ := rC
  obtain ⟨x, y, z, hn, hx, hy, hz, h₁, h₂, h₃⟩ := legendre_box_kernel A B C hA hB hC r s t
  have hd := legendre_box_divisible A B C hAB hBC hCA r s t
    (by simpa [sq] using hr.symm) (by simpa [sq] using hs.symm)
    (by simpa [sq] using ht.symm) x y z h₁ h₂ h₃
  have hx' : x ^ 2 < (B : ℤ) * C := hx.trans_lt (by exact_mod_cast legendre_sqrt_strict _ nBC)
  have hy' : y ^ 2 < (C : ℤ) * A := hy.trans_lt (by exact_mod_cast legendre_sqrt_strict _ nCA)
  have hz' : z ^ 2 < (A : ℤ) * B := hz.trans_lt (by exact_mod_cast legendre_sqrt_strict _ nAB)
  have hA' : (0 : ℤ) < A := by exact_mod_cast hA
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hC' : (0 : ℤ) < C := by exact_mod_cast hC
  have hx'' := mul_lt_mul_of_pos_left hx' hA'
  have hy'' := mul_lt_mul_of_pos_left hy' hB'
  have hz'' := mul_lt_mul_of_pos_left hz' hC'
  have hx₀ : (0 : ℤ) ≤ A * x ^ 2 := by positivity
  have hy₀ : (0 : ℤ) ≤ B * y ^ 2 := by positivity
  have hz₀ : (0 : ℤ) ≤ C * z ^ 2 := by positivity
  rcases legendre_two_values ((A : ℤ) * B * C)
    (-(A : ℤ) * x ^ 2 - (B : ℤ) * y ^ 2 + (C : ℤ) * z ^ 2)
    (by positivity) hd (by nlinarith only [hx'', hy'', hz₀])
    (by nlinarith only [hz'', hx₀, hy₀]) with h | h
  · exact ⟨x, y, z, hn, h⟩
  · simpa only [neg_mul, sub_eq_add_neg] using
      legendre_zero_of_neg_product (-(A : ℤ)) (-B) C x y z
        (by simpa using mul_pos hA' hB') (by nlinarith only [h])

theorem legendre_squarefree_product_square (A B : ℕ) (hA : Squarefree A)
    (hB : Squarefree B) (hAB : A.Coprime B) (hs : IsSquare (A * B)) : A = 1 ∧ B = 1 := by
  have hf : Squarefree (A * B) := (Nat.squarefree_mul hAB).mpr ⟨hA, hB⟩
  obtain ⟨k, hk⟩ := hs
  have hu : IsUnit k := hf k (by rw [hk])
  have hk₁ : k = 1 := Nat.isUnit_iff.mp hu
  rw [hk₁, one_mul] at hk
  exact mul_eq_one.mp hk

/-- Legendre's sufficient residue criterion with two negative coefficients.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, pp. 6–7. -/
theorem legendre_signed_nat (A B C : ℕ)
    (hA : Squarefree A) (hB : Squarefree B) (hC : Squarefree C)
    (hAB : A.Coprime B) (hBC : B.Coprime C) (hCA : C.Coprime A)
    (rA : IsSquare ((B : ZMod A) * C))
    (rB : IsSquare ((C : ZMod B) * A))
    (rC : IsSquare (-((A : ZMod C) * B))) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      -(A : ℤ) * x ^ 2 - (B : ℤ) * y ^ 2 + (C : ℤ) * z ^ 2 = 0 := by
  by_cases nAB : IsSquare (A * B)
  · obtain ⟨rfl, rfl⟩ := legendre_squarefree_product_square A B hA hB hAB nAB
    obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (by simpa using rC)
    refine ⟨x, y, 1, by simp, ?_⟩
    have he : (C : ℤ) = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by exact_mod_cast hxy
    norm_num only [Nat.cast_one, one_pow, one_mul, mul_one] at ⊢
    linarith only [he]
  by_cases nBC : IsSquare (B * C)
  · obtain ⟨rfl, rfl⟩ := legendre_squarefree_product_square B C hB hC hBC nBC
    exact ⟨0, 1, 1, by simp, by ring⟩
  by_cases nCA : IsSquare (C * A)
  · obtain ⟨rfl, rfl⟩ := legendre_squarefree_product_square C A hC hA hCA nCA
    exact ⟨1, 0, 1, by simp, by ring⟩
  exact legendre_of_nonsquare_products A B C (Nat.pos_of_ne_zero hA.ne_zero)
    (Nat.pos_of_ne_zero hB.ne_zero) (Nat.pos_of_ne_zero hC.ne_zero)
    hAB hBC hCA nAB nBC nCA rA rB rC

theorem legendre_two_negative (a b c : ℤ)
    (ha : a < 0) (hb : b < 0) (hc : 0 < c)
    (sa : Squarefree a) (sb : Squarefree b) (sc : Squarefree c)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (ra : IsSquare ((-b * c : ℤ) : ZMod a.natAbs))
    (rb : IsSquare ((-c * a : ℤ) : ZMod b.natAbs))
    (rc : IsSquare ((-a * b : ℤ) : ZMod c.natAbs)) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  have ea : (a.natAbs : ℤ) = -a := by rw [Int.natCast_natAbs, abs_of_neg ha]
  have eb : (b.natAbs : ℤ) = -b := by rw [Int.natCast_natAbs, abs_of_neg hb]
  have ec : (c.natAbs : ℤ) = c := by rw [Int.natCast_natAbs, abs_of_pos hc]
  have eA : a = -(a.natAbs : ℤ) := by omega
  have eB : b = -(b.natAbs : ℤ) := by omega
  have eC : c = (c.natAbs : ℤ) := ec.symm
  have hab' : a.natAbs.Coprime b.natAbs := by
    apply Nat.isCoprime_iff_coprime.mp
    simpa [ea, eb] using hab.neg_left.neg_right
  have hbc' : b.natAbs.Coprime c.natAbs := by
    apply Nat.isCoprime_iff_coprime.mp
    simpa [eb, ec] using hbc.neg_left
  have hca' : c.natAbs.Coprime a.natAbs := by
    apply Nat.isCoprime_iff_coprime.mp
    simpa [ec, ea] using hca.neg_right
  have ra' : IsSquare ((b.natAbs : ZMod a.natAbs) * c.natAbs) := by
    have h : -b * c = (b.natAbs : ℤ) * c.natAbs := by rw [eb, ec]
    simpa only [h, Int.cast_mul, Int.cast_natCast] using ra
  have rb' : IsSquare ((c.natAbs : ZMod b.natAbs) * a.natAbs) := by
    have h : -c * a = (c.natAbs : ℤ) * a.natAbs := by rw [ec, ea]; ring
    simpa only [h, Int.cast_mul, Int.cast_natCast] using rb
  have rc' : IsSquare (-((a.natAbs : ZMod c.natAbs) * b.natAbs)) := by
    have h : -a * b = -((a.natAbs : ℤ) * b.natAbs) := by rw [ea, eb]; ring
    simpa only [h, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using rc
  obtain ⟨x, y, z, hn, he⟩ := legendre_signed_nat a.natAbs b.natAbs c.natAbs
    (Int.squarefree_natAbs.mpr sa) (Int.squarefree_natAbs.mpr sb) (Int.squarefree_natAbs.mpr sc)
    hab' hbc' hca' ra' rb' rc'
  exact ⟨x, y, z, hn, by simpa [ea, eb, ec, sub_eq_add_neg] using he⟩

/-- Legendre's sufficient criterion for squarefree pairwise-coprime integer coefficients.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, pp. 6–7. -/
theorem legendre_integer (a b c : ℤ)
    (sa : Squarefree a) (sb : Squarefree b) (sc : Squarefree c)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (hn : a < 0 ∨ b < 0 ∨ c < 0) (hp : 0 < a ∨ 0 < b ∨ 0 < c)
    (ra : IsSquare ((-b * c : ℤ) : ZMod a.natAbs))
    (rb : IsSquare ((-c * a : ℤ) : ZMod b.natAbs))
    (rc : IsSquare ((-a * b : ℤ) : ZMod c.natAbs)) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  rcases lt_or_gt_of_ne sa.ne_zero with ha | ha <;>
    rcases lt_or_gt_of_ne sb.ne_zero with hb | hb <;>
      rcases lt_or_gt_of_ne sc.ne_zero with hc | hc
  · rcases hp with hp | hp | hp <;> omega
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative a b c
      ha hb hc
      sa sb sc
      (hab) (hbc) (hca)
      (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using ra) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rb) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rc)
    refine ⟨u, v, w, by tauto, ?_⟩
    nlinarith only [he]
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative a c b
      ha hc hb
      sa sc sb
      (hca.symm) (hbc.symm) (hab.symm)
      (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using ra) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rc) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rb)
    refine ⟨u, w, v, by tauto, ?_⟩
    nlinarith only [he]
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative (-b) (-c) (-a)
      (by omega) (by omega) (by omega)
      (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sb) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sc) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sa)
      (hbc.neg_left.neg_right) (hca.neg_left.neg_right) (hab.neg_left.neg_right)
      (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rb) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rc) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using ra)
    refine ⟨w, u, v, by tauto, ?_⟩
    nlinarith only [he]
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative b c a
      hb hc ha
      sb sc sa
      (hbc) (hca) (hab)
      (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rb) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using rc) (by simpa [Int.natAbs_neg, neg_mul, mul_comm] using ra)
    refine ⟨w, u, v, by tauto, ?_⟩
    nlinarith only [he]
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative (-a) (-c) (-b)
      (by omega) (by omega) (by omega)
      (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sa) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sc) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sb)
      (hca.symm.neg_left.neg_right) (hbc.symm.neg_left.neg_right) (hab.symm.neg_left.neg_right)
      (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using ra) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rc) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rb)
    refine ⟨u, w, v, by tauto, ?_⟩
    nlinarith only [he]
  · obtain ⟨u, v, w, hv, he⟩ := legendre_two_negative (-a) (-b) (-c)
      (by omega) (by omega) (by omega)
      (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sa) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sb) (by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg] using sc)
      (hab.neg_left.neg_right) (hbc.neg_left.neg_right) (hca.neg_left.neg_right)
      (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using ra) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rb) (by rw [Int.natAbs_neg]; simpa [neg_mul, mul_comm] using rc)
    refine ⟨u, v, w, by tauto, ?_⟩
    nlinarith only [he]
  · rcases hn with hn | hn | hn <;> omega

/-- The rational zero furnished by the three residue tests.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1, pp. 6–7. -/
theorem legendre_rational (a b c : ℤ)
    (sa : Squarefree a) (sb : Squarefree b) (sc : Squarefree c)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (hn : a < 0 ∨ b < 0 ∨ c < 0) (hp : 0 < a ∨ 0 < b ∨ 0 < c)
    (ra : IsSquare ((-b * c : ℤ) : ZMod a.natAbs))
    (rb : IsSquare ((-c * a : ℤ) : ZMod b.natAbs))
    (rc : IsSquare ((-a * b : ℤ) : ZMod c.natAbs)) :
    ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 + (c : ℚ) * z ^ 2 = 0 := by
  obtain ⟨x, y, z, hn, he⟩ := legendre_integer a b c sa sb sc hab hbc hca hn hp ra rb rc
  refine ⟨x, y, z, ?_, ?_⟩
  · exact_mod_cast hn
  · exact_mod_cast he

example : ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    5 * x ^ 2 + 101 * y ^ 2 - z ^ 2 = 0 := by
  exact ⟨17, 2, 43, by norm_num, by norm_num⟩

example : IsSquare (3 : ZMod 3) ∧ ¬IsSquare (-1 : ZMod 3) := by decide

/-- The overlapping coefficients in the naive two-test criterion have no nonzero zero.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.2, p. 9. -/
theorem three_three_integer (x y z : ℤ) (he : 3 * x ^ 2 + 3 * y ^ 2 = z ^ 2) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have h : ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs = n →
      3 * x ^ 2 + 3 * y ^ 2 = z ^ 2 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y z hzn he
      by_cases hz : z = 0
      · subst z
        have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        exact ⟨hx, hy, rfl⟩
      have hz₃ : (3 : ℤ) ∣ z := by
        have hzz : (3 : ℤ) ∣ z ^ 2 := ⟨x ^ 2 + y ^ 2, by nlinarith only [he]⟩
        exact (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hzz
      obtain ⟨w, hw⟩ := hz₃
      have hxy : x ^ 2 + y ^ 2 = 3 * w ^ 2 := by rw [hw] at he; nlinarith only [he]
      have hm : (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 = 0 := by
        have hh := congrArg (fun v : ℤ => (v : ZMod 3)) hxy
        push_cast at hh
        rw [show (3 : ZMod 3) = 0 by decide, zero_mul] at hh
        exact hh
      have hf : ∀ u v : ZMod 3, u ^ 2 + v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide
      obtain ⟨hx₃, hy₃⟩ := hf _ _ hm
      obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx₃
      obtain ⟨v, hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy₃
      have hn : w.natAbs < n := by
        have hw₀ : w ≠ 0 := by intro h; simp [h] at hw; exact hz hw
        have hwpos := Int.natAbs_pos.mpr hw₀
        rw [← hzn, hw, Int.natAbs_mul]
        norm_num
        omega
      obtain ⟨hu₀, hv₀, hw₀⟩ := ih w.natAbs hn u v w rfl (by rw [hu, hv] at hxy; norm_num at hxy; nlinarith only [hxy])
      simp_all
  exact h z.natAbs x y z rfl he

theorem ternary_clear_denominators (x y z : ℚ) :
    ∃ d : ℚ, d ≠ 0 ∧ ∃ u v w : ℤ,
      (u : ℚ) = d * x ∧ (v : ℚ) = d * y ∧ (w : ℚ) = d * z := by
  have hx : (x.num : ℚ) = x * x.den :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * y.den :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  have hz : (z.num : ℚ) = z * z.den :=
    (div_eq_iff (by exact_mod_cast z.den_ne_zero)).mp (Rat.num_div_den z)
  refine ⟨(x.den : ℚ) * y.den * z.den, by positivity,
    x.num * y.den * z.den, y.num * x.den * z.den, z.num * x.den * y.den, ?_, ?_, ?_⟩
  · push_cast
    rw [hx]
    ring
  · push_cast
    rw [hy]
    ring
  · push_cast
    rw [hz]
    ring

/-- The naive residue tests at `a = b = 3` do not yield a rational zero.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.2, p. 9. -/
theorem three_three_rational (x y z : ℚ) (he : 3 * x ^ 2 + 3 * y ^ 2 = z ^ 2) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  obtain ⟨d, hd, u, v, w, hu, hv, hw⟩ := ternary_clear_denominators x y z
  have hi : 3 * u ^ 2 + 3 * v ^ 2 = w ^ 2 := by
    have hh : (3 : ℚ) * (u : ℚ) ^ 2 + 3 * (v : ℚ) ^ 2 = (w : ℚ) ^ 2 := by
      rw [hu, hv, hw]
      linear_combination d ^ 2 * he
    exact_mod_cast hh
  obtain ⟨rfl, rfl, rfl⟩ := three_three_integer u v w hi
  simp only [Int.cast_zero, eq_comm, mul_eq_zero, hd, false_or] at hu hv hw
  exact ⟨hu, hv, hw⟩

theorem minimal_diagonal_squarefree (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hmin : ∀ (A B C : ℤ) (k u v w : ℚ), k ≠ 0 → u ≠ 0 → v ≠ 0 → w ≠ 0 →
      (a : ℚ) = k * A * u ^ 2 → (b : ℚ) = k * B * v ^ 2 →
      (c : ℚ) = k * C * w ^ 2 → (a * b * c).natAbs ≤ (A * B * C).natAbs) :
    Squarefree a := by
  intro d hd
  obtain ⟨t, ht⟩ := hd
  have hd₀ : d ≠ 0 := by intro h; simp [h] at ht; exact ha ht
  have ht₀ : t ≠ 0 := by intro h; simp [h] at ht; exact ha ht
  have hbound := hmin t b c 1 d 1 1 one_ne_zero (Int.cast_ne_zero.mpr hd₀)
    one_ne_zero one_ne_zero (by exact_mod_cast (show a = 1 * t * d ^ 2 by nlinarith only [ht]))
    (by simp) (by simp)
  have he : (a * b * c).natAbs = d.natAbs ^ 2 * (t * b * c).natAbs := by
    rw [ht]
    simp only [Int.natAbs_mul]
    ring
  have hp : 0 < (t * b * c).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (mul_ne_zero ht₀ hb) hc)
  rw [he] at hbound
  have hle : d.natAbs ^ 2 ≤ 1 := by nlinarith only [hbound, hp]
  have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd₀
  apply Int.isUnit_iff_natAbs_eq.mpr
  nlinarith only [hle, hpos]

theorem minimal_diagonal_coprime (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hmin : ∀ (A B C : ℤ) (k u v w : ℚ), k ≠ 0 → u ≠ 0 → v ≠ 0 → w ≠ 0 →
      (a : ℚ) = k * A * u ^ 2 → (b : ℚ) = k * B * v ^ 2 →
      (c : ℚ) = k * C * w ^ 2 → (a * b * c).natAbs ≤ (A * B * C).natAbs) :
    IsCoprime a b := by
  apply IsRelPrime.isCoprime
  intro d hda hdb
  obtain ⟨t, ht⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  have hd₀ : d ≠ 0 := by intro h; simp [h] at ht; exact ha ht
  have ht₀ : t ≠ 0 := by intro h; simp [h] at ht; exact ha ht
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs; exact hb hs
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd₀
  have hbound := hmin t s (d * c) (d : ℚ)⁻¹ d d 1 (inv_ne_zero hdQ) hdQ hdQ one_ne_zero
    (by rw [ht]; push_cast; field_simp)
    (by rw [hs]; push_cast; field_simp)
    (by push_cast; field_simp)
  have he : (a * b * c).natAbs = d.natAbs * (t * s * (d * c)).natAbs := by
    rw [ht, hs]
    simp only [Int.natAbs_mul]
    ring
  have hp : 0 < (t * s * (d * c)).natAbs :=
    Int.natAbs_pos.mpr (mul_ne_zero (mul_ne_zero ht₀ hs₀) (mul_ne_zero hd₀ hc))
  rw [he] at hbound
  have hle : d.natAbs ≤ 1 := by nlinarith only [hbound, hp]
  have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd₀
  exact Int.isUnit_iff_natAbs_eq.mpr (by omega)

/-- A regular rational diagonal has a squarefree pairwise-coprime integral model,
up to a nonzero common multiplier and invertible diagonal coordinate changes.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2, p. 5. -/
theorem ternary_normalization (A B C : ℚ) (hA₀ : A ≠ 0) (hB₀ : B ≠ 0) (hC₀ : C ≠ 0) :
    ∃ a b c : ℤ, Squarefree a ∧ Squarefree b ∧ Squarefree c ∧
      IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c a ∧
      ∃ k u v w : ℚ, k ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
        A = k * a * u ^ 2 ∧ B = k * b * v ^ 2 ∧ C = k * c * w ^ 2 := by
  classical
  have hex : ∃ n : ℕ, ∃ (a b c : ℤ) (k u v w : ℚ),
      k ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
      A = k * a * u ^ 2 ∧ B = k * b * v ^ 2 ∧ C = k * c * w ^ 2 ∧
      (a * b * c).natAbs = n := by
    obtain ⟨d, hd, a, b, c, ha, hb, hc⟩ := ternary_clear_denominators A B C
    refine ⟨(a * b * c).natAbs, a, b, c, d⁻¹, 1, 1, 1,
      inv_ne_zero hd, one_ne_zero, one_ne_zero, one_ne_zero, ?_, ?_, ?_, rfl⟩
    · rw [ha]; field_simp
    · rw [hb]; field_simp
    · rw [hc]; field_simp
  obtain ⟨a, b, c, k, u, v, w, hk, hu, hv, hw, hA, hB, hC, hn⟩ := Nat.find_spec hex
  have ha : a ≠ 0 := by intro ha; simp [ha] at hA; exact hA₀ hA
  have hb : b ≠ 0 := by intro hb; simp [hb] at hB; exact hB₀ hB
  have hc : c ≠ 0 := by intro hc; simp [hc] at hC; exact hC₀ hC
  have hm : ∀ (a' b' c' : ℤ) (k' u' v' w' : ℚ),
      k' ≠ 0 → u' ≠ 0 → v' ≠ 0 → w' ≠ 0 →
      (a : ℚ) = k' * a' * u' ^ 2 → (b : ℚ) = k' * b' * v' ^ 2 →
      (c : ℚ) = k' * c' * w' ^ 2 → (a * b * c).natAbs ≤ (a' * b' * c').natAbs := by
    intro a' b' c' k' u' v' w' hk' hu' hv' hw' ha' hb' hc'
    rw [hn]
    apply Nat.find_min' hex
    refine ⟨a', b', c', k * k', u * u', v * v', w * w',
      mul_ne_zero hk hk', mul_ne_zero hu hu', mul_ne_zero hv hv', mul_ne_zero hw hw',
      ?_, ?_, ?_, rfl⟩
    · rw [hA, ha']; ring
    · rw [hB, hb']; ring
    · rw [hC, hc']; ring
  have hm' : ∀ (a' b' c' : ℤ) (k' u' v' w' : ℚ),
      k' ≠ 0 → u' ≠ 0 → v' ≠ 0 → w' ≠ 0 →
      (b : ℚ) = k' * a' * u' ^ 2 → (c : ℚ) = k' * b' * v' ^ 2 →
      (a : ℚ) = k' * c' * w' ^ 2 → (b * c * a).natAbs ≤ (a' * b' * c').natAbs := by
    intro a' b' c' k' u' v' w' hk' hu' hv' hw' hb' hc' ha'
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hm c' a' b' k' w' u' v' hk' hw' hu' hv' ha' hb' hc'
  have hm'' : ∀ (a' b' c' : ℤ) (k' u' v' w' : ℚ),
      k' ≠ 0 → u' ≠ 0 → v' ≠ 0 → w' ≠ 0 →
      (c : ℚ) = k' * a' * u' ^ 2 → (a : ℚ) = k' * b' * v' ^ 2 →
      (b : ℚ) = k' * c' * w' ^ 2 → (c * a * b).natAbs ≤ (a' * b' * c').natAbs := by
    intro a' b' c' k' u' v' w' hk' hu' hv' hw' hc' ha' hb'
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hm b' c' a' k' v' w' u' hk' hv' hw' hu' ha' hb' hc'
  exact ⟨a, b, c, minimal_diagonal_squarefree a b c ha hb hc hm,
    minimal_diagonal_squarefree b c a hb hc ha hm',
    minimal_diagonal_squarefree c a b hc ha hb hm'',
    minimal_diagonal_coprime a b c ha hb hc hm,
    minimal_diagonal_coprime b c a hb hc ha hm',
    minimal_diagonal_coprime c a b hc ha hb hm'',
    k, u, v, w, hk, hu, hv, hw, hA, hB, hC⟩

/-- Reduction of an arbitrary regular rational ternary form to the integral model.
Source: Serre, A Course in Arithmetic, Chapter IV, §1; Shurman, §2, p. 5. -/
theorem regular_ternary_normalization {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
    (hQ : Q.associated.SeparatingLeft) (hdim : Module.finrank ℚ V = 3) :
    ∃ (e : V ≃ₗ[ℚ] (Fin 3 → ℚ)) (a b c : ℤ),
      Squarefree a ∧ Squarefree b ∧ Squarefree c ∧
      IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c a ∧
      ∃ k u v w : ℚ, k ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
        ∀ x : V, Q x = k * ((a : ℚ) * (u * e x 0) ^ 2 +
          (b : ℚ) * (v * e x 1) ^ 2 + (c : ℚ) * (w * e x 2) ^ 2) := by
  have hdiag : ∃ d : Fin 3 → ℚˣ,
      Q.Equivalent (QuadraticMap.weightedSumSquares ℚ d) := by
    have h := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
    rw [hdim] at h
    exact h
  obtain ⟨d, ⟨e⟩⟩ := hdiag
  obtain ⟨a, b, c, sa, sb, sc, hab, hbc, hca, k, u, v, w, hk, hu, hv, hw, hA, hB, hC⟩ :=
    ternary_normalization (d 0) (d 1) (d 2) (d 0).ne_zero (d 1).ne_zero (d 2).ne_zero
  refine ⟨e.toLinearEquiv, a, b, c, sa, sb, sc, hab, hbc, hca, k, u, v, w,
    hk, hu, hv, hw, ?_⟩
  intro x
  change Q x = k * ((a : ℚ) * (u * e x 0) ^ 2 +
    (b : ℚ) * (v * e x 1) ^ 2 + (c : ℚ) * (w * e x 2) ^ 2)
  have he := e.map_app x
  simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three,
    Units.smul_def, smul_eq_mul] at he
  change (d 0 : ℚ) * (e x 0 * e x 0) + (d 1 : ℚ) * (e x 1 * e x 1) +
    (d 2 : ℚ) * (e x 2 * e x 2) = Q x at he
  rw [hA, hB, hC] at he
  convert he.symm using 1 <;> ring

theorem padic_primitive_vector (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι]
    (v : ι → ℚ_[p]) (hv : v ≠ 0) :
    ∃ d : ℚ_[p], d ≠ 0 ∧ ∃ w : ι → ℤ_[p],
      (∀ i, v i = d * w i) ∧ ∃ i, IsUnit (w i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
    ⟨j, Finset.mem_univ _⟩
  have hd : v i ≠ 0 := by
    intro he
    have hh := hi j (Finset.mem_univ _)
    rw [he, norm_zero] at hh
    exact hj (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  let w : ι → ℤ_[p] := fun j => ⟨v j / v i, by
    change ‖v j / v i‖ ≤ 1
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hd)).mpr (hi j (Finset.mem_univ _))⟩
  refine ⟨v i, hd, w, fun j => ?_, i, ?_⟩
  · change v j = v i * (v j / v i)
    field_simp
  · apply PadicInt.isUnit_iff.mpr
    change ‖v i / v i‖ = 1
    rw [div_self hd, norm_one]

theorem square_neg_product_of_binary_zero {K : Type*} [Field K] (b c y z : K)
    (hy : y ≠ 0) (he : b * y ^ 2 + c * z ^ 2 = 0) : IsSquare (-b * c) := by
  refine ⟨c * z / y, ?_⟩
  field_simp
  linear_combination -c * he

theorem primitive_prime_residue (p : ℕ) [Fact p.Prime] (a b c : ℤ)
    (sa : Squarefree a) (hp : (p : ℤ) ∣ a)
    (x y z : ℤ_[p]) (hu : IsUnit x ∨ IsUnit y ∨ IsUnit z)
    (he : (a : ℤ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    IsSquare ((-b * c : ℤ) : ZMod p) := by
  have ha₀ : (a : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hp
  have hr := congrArg PadicInt.toZMod he
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero, ha₀, zero_mul, zero_add] at hr
  by_cases hy : PadicInt.toZMod y = 0
  · by_cases hz : PadicInt.toZMod z = 0
    · have hx : IsUnit x := hu.resolve_right (by
        rintro (h | h)
        · exact (h.map PadicInt.toZMod).ne_zero hy
        · exact (h.map PadicInt.toZMod).ne_zero hz)
      have hdiv : ∀ v : ℤ_[p], PadicInt.toZMod v = 0 → (p : ℤ_[p]) ∣ v := by
        intro v hv
        rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
          ← PadicInt.ker_toZMod, RingHom.mem_ker]
        exact hv
      obtain ⟨Y, hY⟩ := hdiv y hy
      obtain ⟨Z, hZ⟩ := hdiv z hz
      have hpp : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      have hyy : (PadicInt.toZModPow 2 y) ^ 2 = 0 := by
        rw [hY, map_mul, map_natCast, mul_pow, hpp, zero_mul]
      have hzz : (PadicInt.toZModPow 2 z) ^ 2 = 0 := by
        rw [hZ, map_mul, map_natCast, mul_pow, hpp, zero_mul]
      have hr₂ := congrArg (PadicInt.toZModPow 2) he
      simp only [map_add, map_mul, map_pow, map_intCast, map_zero,
        hyy, hzz, mul_zero, add_zero] at hr₂
      have ha₂ : (a : ZMod (p ^ 2)) = 0 :=
        ((hx.map (PadicInt.toZModPow 2)).pow 2).mul_right_cancel (by simpa using hr₂)
      have hd : (p : ℤ) * p ∣ a := by
        simpa [sq] using (ZMod.intCast_zmod_eq_zero_iff_dvd a (p ^ 2)).mp ha₂
      have hunit := sa (p : ℤ) hd
      exact False.elim ((Fact.out : p.Prime).ne_one (by
        simpa using Int.isUnit_iff_natAbs_eq.mp hunit))
    · have hs := square_neg_product_of_binary_zero (c : ZMod p) b
        (PadicInt.toZMod z) (PadicInt.toZMod y) hz (by linear_combination hr)
      simpa [mul_comm] using hs
  · have hs := square_neg_product_of_binary_zero (b : ZMod p) c
      (PadicInt.toZMod y) (PadicInt.toZMod z) hy hr
    simpa using hs

theorem square_mod_squarefree (n : ℕ) (hn : Squarefree n) (a : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → IsSquare (a : ZMod p)) :
    IsSquare (a : ZMod n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn₁ : n = 1
    · subst n
      exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hn₁
    obtain ⟨m, rfl⟩ := hd
    have hm₀ : m ≠ 0 := by intro hm; simp [hm] at hn
    have hcop := Nat.coprime_of_squarefree_mul hn
    have hm : m < p * m := by nlinarith [hp.two_le, Nat.pos_of_ne_zero hm₀]
    obtain ⟨x, hx⟩ := h p hp (dvd_mul_right _ _)
    obtain ⟨y, hy⟩ := ih m hm hn.of_mul_right
      (fun q hq hd => h q hq (dvd_mul_of_dvd_right hd p))
    let e := ZMod.chineseRemainder hcop
    refine ⟨e.symm (x, y), ?_⟩
    apply e.injective
    rw [map_mul, e.apply_symm_apply]
    apply Prod.ext
    · simpa [e, ZMod.chineseRemainder, ZMod.cast_intCast (dvd_mul_right p m)] using hx
    · simpa [e, ZMod.chineseRemainder, ZMod.cast_intCast (dvd_mul_left m p)] using hy

theorem local_ternary_residue (a b c : ℤ) (sa : Squarefree a)
    (hl : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p],
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    IsSquare ((-b * c : ℤ) : ZMod a.natAbs) := by
  apply square_mod_squarefree _ (Int.squarefree_natAbs.mpr sa)
  intro p hp hd
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, z, hn, he⟩ := hl p
  have hv : (![x, y, z] : Fin 3 → ℚ_[p]) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Pi.zero_apply] at h0 h1 h2
    tauto
  obtain ⟨d, hd₀, w, hw, i, hi⟩ := padic_primitive_vector p ![x, y, z] hv
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  change z = d * (w 2 : ℚ_[p]) at h2
  have hwzero : (a : ℤ_[p]) * w 0 ^ 2 + b * w 1 ^ 2 + c * w 2 ^ 2 = 0 := by
    apply Subtype.ext
    change (a : ℚ_[p]) * (w 0 : ℚ_[p]) ^ 2 + b * (w 1 : ℚ_[p]) ^ 2 +
      c * (w 2 : ℚ_[p]) ^ 2 = 0
    rw [h0, h1, h2] at he
    have hf : d ^ 2 * ((a : ℚ_[p]) * (w 0 : ℚ_[p]) ^ 2 +
        b * (w 1 : ℚ_[p]) ^ 2 + c * (w 2 : ℚ_[p]) ^ 2) = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hf).resolve_left (pow_ne_zero 2 hd₀)
  apply primitive_prime_residue p a b c sa (Int.natCast_dvd.mpr hd) (w 0) (w 1) (w 2)
  · fin_cases i <;> tauto
  · exact hwzero

theorem ternary_real_signs (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (x y z : ℝ) (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (he : (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    (a < 0 ∨ b < 0 ∨ c < 0) ∧ (0 < a ∨ 0 < b ∨ 0 < c) := by
  have aux : ∀ A B C : ℝ, 0 < A → 0 < B → 0 < C →
      A * x ^ 2 + B * y ^ 2 + C * z ^ 2 ≠ 0 := by
    intro A B C hA hB hC heq
    have hx : 0 ≤ A * x ^ 2 := mul_nonneg hA.le (sq_nonneg x)
    have hy : 0 ≤ B * y ^ 2 := mul_nonneg hB.le (sq_nonneg y)
    have hz : 0 ≤ C * z ^ 2 := mul_nonneg hC.le (sq_nonneg z)
    rcases hn with hn | hn | hn
    · have := mul_pos hA (sq_pos_of_ne_zero hn); linarith
    · have := mul_pos hB (sq_pos_of_ne_zero hn); linarith
    · have := mul_pos hC (sq_pos_of_ne_zero hn); linarith
  constructor
  · by_contra! h
    exact aux a b c (by exact_mod_cast lt_of_le_of_ne h.1 (Ne.symm ha))
      (by exact_mod_cast lt_of_le_of_ne h.2.1 (Ne.symm hb))
      (by exact_mod_cast lt_of_le_of_ne h.2.2 (Ne.symm hc)) he
  · by_contra! h
    apply aux (-a) (-b) (-c)
      (by exact_mod_cast neg_pos.mpr (lt_of_le_of_ne h.1 ha))
      (by exact_mod_cast neg_pos.mpr (lt_of_le_of_ne h.2.1 hb))
      (by exact_mod_cast neg_pos.mpr (lt_of_le_of_ne h.2.2 hc))
    linear_combination -he

theorem rational_ternary_baseChange {K : Type*} [Field K] [CharZero K]
    (a b c : ℚ)
    (h : ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : K) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨x, y, z, hn, he⟩ := h
  refine ⟨x, y, z, ?_, ?_⟩
  · simpa only [ne_eq, Rat.cast_eq_zero] using hn
  · exact_mod_cast he

/-- The squarefree integral criterion is equivalent to isotropy at every place.
Source: Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1;
Serre, A Course in Arithmetic, Chapter IV, §3.2, Theorem 8. -/
theorem legendre_local_global_integral (a b c : ℤ)
    (sa : Squarefree a) (sb : Squarefree b) (sc : Squarefree c)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) :
    (∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : ℚ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
    (∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ∧
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p],
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) := by
  constructor
  · intro h
    constructor
    · simpa only [Rat.cast_intCast] using
        (rational_ternary_baseChange (K := ℝ) a b c h)
    · intro p _
      simpa only [Rat.cast_intCast] using
        (rational_ternary_baseChange (K := ℚ_[p]) a b c h)
  · rintro ⟨⟨x, y, z, hn, he⟩, hl⟩
    obtain ⟨hn, hp⟩ := ternary_real_signs a b c sa.ne_zero sb.ne_zero sc.ne_zero x y z hn he
    apply legendre_rational a b c sa sb sc hab hbc hca hn hp
    · exact local_ternary_residue a b c sa hl
    · apply local_ternary_residue b c a sb
      intro p _
      obtain ⟨x, y, z, hn, he⟩ := hl p
      exact ⟨y, z, x, by tauto, by linear_combination he⟩
    · apply local_ternary_residue c a b sc
      intro p _
      obtain ⟨x, y, z, hn, he⟩ := hl p
      exact ⟨z, x, y, by tauto, by linear_combination he⟩

theorem ternary_diagonal_transport {K : Type*} [Field K]
    (a b c k u v w : K) (hk : k ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (k * a * u ^ 2) * x ^ 2 + (k * b * v ^ 2) * y ^ 2 +
        (k * c * w ^ 2) * z ^ 2 = 0) ↔
    (∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) := by
  constructor
  · rintro ⟨x, y, z, hn, he⟩
    refine ⟨u * x, v * y, w * z, ?_, ?_⟩
    · rcases hn with hn | hn | hn
      · exact Or.inl (mul_ne_zero hu hn)
      · exact Or.inr (Or.inl (mul_ne_zero hv hn))
      · exact Or.inr (Or.inr (mul_ne_zero hw hn))
    · apply (mul_eq_zero.mp (show k * (a * (u * x) ^ 2 + b * (v * y) ^ 2 +
          c * (w * z) ^ 2) = 0 by linear_combination he)).resolve_left hk
  · rintro ⟨x, y, z, hn, he⟩
    refine ⟨x / u, y / v, z / w, ?_, ?_⟩
    · rcases hn with hn | hn | hn
      · exact Or.inl (div_ne_zero hn hu)
      · exact Or.inr (Or.inl (div_ne_zero hn hv))
      · exact Or.inr (Or.inr (div_ne_zero hn hw))
    · simp only [div_pow]
      field_simp
      linear_combination k * he

/-- A regular rational diagonal ternary form is isotropic exactly when it is
isotropic over the reals and every prime-adic field.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, Theorem 8;
Shurman, Ternary Quadratic Forms: Lagrange and Legendre, §2.1. -/
theorem ternary_local_global (A B C : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      A * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0) ↔
    (∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (A : ℝ) * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0) ∧
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p],
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (A : ℚ_[p]) * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0) := by
  constructor
  · intro h
    exact ⟨rational_ternary_baseChange A B C h,
      fun p _ => rational_ternary_baseChange A B C h⟩
  · intro hl
    obtain ⟨a, b, c, sa, sb, sc, hab, hbc, hca, k, u, v, w,
      hk, hu, hv, hw, hA', hB', hC'⟩ := ternary_normalization A B C hA hB hC
    have transfer (K : Type) [Field K] [CharZero K] :
        (∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
          (A : K) * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0) ↔
        (∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
          (a : K) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) := by
      rw [hA', hB', hC']
      simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast]
      exact ternary_diagonal_transport (a : K) (b : K) (c : K) (k : K) (u : K) (v : K) (w : K)
        (Rat.cast_ne_zero.mpr hk) (Rat.cast_ne_zero.mpr hu)
        (Rat.cast_ne_zero.mpr hv) (Rat.cast_ne_zero.mpr hw)
    apply (transfer ℚ).mpr
    apply (legendre_local_global_integral a b c sa sb sc hab hbc hca).mpr
    exact ⟨(transfer ℝ).mp hl.1, fun p _ => (transfer ℚ_[p]).mp (hl.2 p)⟩

end HodgeLean.Foundations.MeyerRational
