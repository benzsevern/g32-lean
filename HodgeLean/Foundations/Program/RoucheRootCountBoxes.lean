import HodgeLean.Foundations.Program.RoucheRootCountLemmas
import HodgeLean.Foundations.Program.BraidCertificateDefs

/-! # The sextics as complex polynomials, and isolating squares from Pellet discs

The coefficients `rou_sextic ε` define a complex polynomial whose evaluation is `b65r_P ε`; its
Taylor coefficients at `a + b i` are the Gaussian rationals `rou_shift`, and `|re| + |im|`
majorizes their moduli, so the rational inequalities give the Pellet hypothesis. A root count of
one in `D(c, h)` and in `D(c, 3h/2)` gives exactly one root in the open square of half-side `h`.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

open Polynomial Complex Metric

/-- The Gaussian rational `(x, y)` as the complex number `x + y i`.
Source: B65-BRAIDCERT checker part A, arithmetic over `ℚ(i)`. -/
def rou_toC (v : ℚ × ℚ) : ℂ := (v.1 : ℂ) + (v.2 : ℂ) * I

/-- The complex polynomial with coefficients `rou_sextic ε`.
Source: G32 v0.16, §5.2, P₅ and P₋₇. -/
def rou_sexticPoly (ε : ℚ) : ℂ[X] := ∑ j : Fin 7, C ((rou_sextic ε j : ℚ) : ℂ) * X ^ (j : ℕ)

theorem rou_sexticPoly_eval (ε : ℚ) (z : ℂ) : (rou_sexticPoly ε).eval z = b65r_P ε z := by
  simp [rou_sexticPoly, rou_sextic, b65r_P, Fin.sum_univ_succ]
  ring

theorem rou_sexticPoly_natDegree (ε : ℚ) : (rou_sexticPoly ε).natDegree ≤ 6 :=
  natDegree_sum_le_of_forall_le _ _ fun j _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.isLt)

theorem rou_toC_gpow (a b : ℚ) (n : ℕ) :
    rou_toC (rou_gpow a b n) = ((a : ℂ) + (b : ℂ) * I) ^ n := by
  induction n with
  | zero => simp [rou_toC, rou_gpow]
  | succ n ih =>
    rw [pow_succ, ← ih]
    simp only [rou_toC, rou_gpow]
    push_cast
    linear_combination (-((rou_gpow a b n).2 : ℂ) * b) * I_sq

theorem rou_toC_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ × ℚ) :
    rou_toC (∑ i ∈ s, f i) = ∑ i ∈ s, rou_toC (f i) := by
  simp [rou_toC, Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib, Finset.sum_mul]

theorem rou_toC_smul (t : ℚ) (v : ℚ × ℚ) : rou_toC (t • v) = t * rou_toC v := by
  simp [rou_toC]; ring

theorem rou_taylor_coeff (ε a b : ℚ) (k : ℕ) :
    (taylor ((a : ℂ) + (b : ℂ) * I) (rou_sexticPoly ε)).coeff k =
      rou_toC (rou_shift (rou_sextic ε) a b k) := by
  rw [rou_shift, rou_toC_sum, rou_sexticPoly, map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_mul_X_pow_eq_monomial, taylor_monomial, coeff_C_mul, coeff_X_add_C_pow, rou_toC_smul,
    rou_toC_gpow]
  push_cast
  ring

theorem rou_norm_toC_le (v : ℚ × ℚ) : ‖rou_toC v‖ ≤ (rou_l1 v : ℝ) := by
  refine (norm_add_le _ _).trans ?_
  simp [rou_l1, Complex.norm_ratCast]

theorem rou_norm_toC_sq (v : ℚ × ℚ) : ‖rou_toC v‖ ^ 2 = (rou_normSq v : ℝ) := by
  have : rou_toC v = ((v.1 : ℝ) : ℂ) + ((v.2 : ℝ) : ℂ) * I := by simp [rou_toC]
  rw [Complex.sq_norm, this, normSq_add_mul_I, rou_normSq]
  push_cast; ring

/-- The rational one-zero inequality at radius `ρ` gives one root of the sextic in `D(c, ρ)`. -/
theorem rou_sextic_pellet_one (ε a b ρ : ℚ) (hρ : 0 < ρ)
    (h : rou_ratTail (rou_sextic ε) a b ρ 1 ^ 2 <
      rou_normSq (rou_shift (rou_sextic ε) a b 1) * ρ ^ 2) :
    rou_discCount (rou_sexticPoly ε) ((a : ℂ) + (b : ℂ) * I) ρ = 1 := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  apply rou_pellet_one_poly _ _ _ hρ'
  have hT : rou_pelletTail (rou_sexticPoly ε) ((a : ℂ) + (b : ℂ) * I) ρ 1 ≤
      (rou_ratTail (rou_sextic ε) a b ρ 1 : ℝ) := by
    rw [rou_pelletTail, rou_ratTail]
    push_cast
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset_erase _ (Finset.range_subset_range.2 ?_))
      fun k _ _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ'.le k)).trans
      (Finset.sum_le_sum fun k _ => ?_)
    · rw [natDegree_taylor]
      have := rou_sexticPoly_natDegree ε
      omega
    · rw [rou_taylor_coeff]
      exact mul_le_mul_of_nonneg_right (rou_norm_toC_le _) (pow_nonneg hρ'.le k)
  have hT0 := (rou_pelletTail_nonneg (rou_sexticPoly ε) ((a : ℂ) + (b : ℂ) * I) hρ'.le 1).trans hT
  have hsq : (rou_ratTail (rou_sextic ε) a b ρ 1 : ℝ) ^ 2 <
      (‖(taylor ((a : ℂ) + (b : ℂ) * I) (rou_sexticPoly ε)).coeff 1‖ * ρ) ^ 2 := by
    rw [mul_pow, rou_taylor_coeff, rou_norm_toC_sq]
    exact_mod_cast h
  exact hT.trans_lt (lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq)

/-- One root in `D(c, h)` and one in `D(c, 3h/2)`, with multiplicity, give exactly one root in
the open square of half-side `h` about `c`, since `D(c, h) ⊆ square ⊆ D(c, 3h/2)`. -/
theorem rou_square_unique (P : ℂ[X]) (c : ℂ) (h : ℝ) (hh : 0 < h)
    (h1 : rou_discCount P c h = 1) (h2 : rou_discCount P c (3 / 2 * h) = 1) :
    ∃! z : ℂ, |z.re - c.re| < h ∧ |z.im - c.im| < h ∧ P.eval z = 0 := by
  classical
  have hP : P ≠ 0 := by
    rintro rfl
    simp [rou_discCount] at h1
  have hin : ∀ z : ℂ, |z.re - c.re| < h → |z.im - c.im| < h → z ∈ ball c (3 / 2 * h) := by
    intro z hx hy
    rw [mem_ball, dist_eq_norm]
    have hs : ‖z - c‖ ^ 2 < (3 / 2 * h) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im]
      have hx2 := (sq_lt_sq' (abs_lt.1 hx).1 (abs_lt.1 hx).2)
      have hy2 := (sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2)
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hs
  rw [rou_discCount] at h1 h2
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 (h1 ▸ Nat.one_pos)
  rw [Multiset.mem_filter, mem_roots hP] at hz
  have hzb := hz.2
  rw [mem_ball, dist_eq_norm] at hzb
  refine ⟨z, ⟨by simpa using (abs_re_le_norm (z - c)).trans_lt hzb,
    by simpa using (abs_im_le_norm (z - c)).trans_lt hzb, hz.1⟩, ?_⟩
  rintro y ⟨hx, hy, hy0⟩
  by_contra hne
  have hsub : ({y, z} : Multiset ℂ) ≤ P.roots.filter (· ∈ ball c (3 / 2 * h)) := by
    rw [Multiset.le_iff_subset (by simp [hne])]
    intro w hw
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hw
    rw [Multiset.mem_filter, mem_roots hP]
    rcases hw with rfl | rfl
    · exact ⟨hy0, hin w hx hy⟩
    · exact ⟨hz.1, ball_subset_ball (by linarith) hz.2⟩
  have := Multiset.card_le_card hsub
  rw [h2] at this
  simp at this

end HodgeLean.Foundations.Program
