import HodgeLean.Foundations.Program.KernelFramesFamilyDefs
import HodgeLean.Foundations.Program.KernelFramesBase

/-! # B6-5 stage 5d, family part: the labelled reflection poles at the base parameter

From the record field `b65p_Outputs.base_coefficient`, the six labels over each fibre are the
roots of the monic fibre polynomial (`b65q_fibre_prod`); hence power sums, inverse power sums
about the fixed poles, and mixed sums over the labels of a fibre take the rational values of the
companion-matrix traces of `KernelFrames.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65q_fibreSet (e : Fin 2) : Finset (Fin 12) :=
  Finset.univ.filter fun x ↦ b65q_fibreIndex x = e

theorem b65q_fibreSet_zero : b65q_fibreSet 0 = {1, 3, 5, 6, 9, 10} := by decide
theorem b65q_fibreSet_one : b65q_fibreSet 1 = {0, 2, 4, 7, 8, 11} := by decide

/-- The polynomial `b65r_P ε` over `ℂ`. -/
def b65q_PC (ε : ℂ) : ℂ[X] := X ^ 2 * (X - 3) ^ 4 - C ε * (X - 1) ^ 3 * (X + 2) ^ 3

theorem b65q_PC_eval (ε s : ℂ) : (b65q_PC ε).eval s = b65r_P ε s := by
  simp [b65q_PC, b65r_P]

theorem b65q_deriv_P (ε s : ℂ) : deriv (b65r_P ε) s = (b65q_PC ε).derivative.eval s := by
  rw [show b65r_P ε = fun s ↦ (b65q_PC ε).eval s from funext fun s ↦ (b65q_PC_eval ε s).symm]
  exact Polynomial.deriv _

theorem b65q_base_logDeriv {p : Fin 12 → ℂ} (O : b65p_Outputs p) (s : ℂ) (hs : s ∈ b65s_regular) :
    (∑ x ∈ b65q_fibreSet 0, (s - p x)⁻¹) = (b65q_PC 5).derivative.eval s / (b65q_PC 5).eval s ∧
    (∑ x ∈ b65q_fibreSet 1, (s - p x)⁻¹) =
      (b65q_PC (-7)).derivative.eval s / (b65q_PC (-7)).eval s := by
  have h := O.base_coefficient s hs
  rw [O.residue_zero] at h
  have h1 := congrArg (fun L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ L (Pi.single 0 1) 1) h
  have h2 := congrArg (fun L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ L (Pi.single 2 1) 2) h
  simp only [b65p_coefficient, b65r_pullback, b65p_initialResidue, Fintype.sum_sum_type,
    _root_.add_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, Pi.add_apply, Sum.elim_inl, Sum.elim_inr,
    b65r_operator, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one, smul_eq_mul, b65q_deriv_P] at h1 h2
  rw [b65q_fibreSet_zero, b65q_fibreSet_one]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_poles, b65p_fixedPole, b65p_fixedResidue,
    b65p_movingResidue, b65p_fibre, b65r_Binf, b65r_B0, b65r_B5, b65r_Bneg7, Matrix.col_apply,
    Sum.elim_inr, Sum.elim_inl, zero_mul, add_zero] at h1 h2
  norm_num [Matrix.diagonal, b65r_B5, b65r_Bneg7, ← b65q_PC_eval] at h1 h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  try norm_num
  constructor
  · linear_combination (648 / 119 : ℂ) * h1
  · linear_combination (135 / 56 : ℂ) * h2

/-- The monic fibre polynomial `P_ε/(1 − ε)` over `ℂ`. -/
def b65q_fibreC (e : Fin 2) : ℂ[X] :=
  C (1 - ((b65q_fibreValue e : ℤ) : ℂ))⁻¹ * b65q_PC ((b65q_fibreValue e : ℤ) : ℂ)

/-- Coefficients of the monic fibre polynomials, in increasing degree. -/
def b65q_fibreCoeff : Fin 2 → Fin 7 → ℚ :=
  ![![-10, 15, -51/4, 53/4, -69/4, 27/4, 1], ![-7, 21/2, 123/8, -185/8, 33/8, 9/8, 1]]

theorem b65q_fibreC_eq (e : Fin 2) :
    b65q_fibreC e = ∑ i : Fin 7, C ((b65q_fibreCoeff e i : ℚ) : ℂ) * X ^ (i : ℕ) := by
  apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  fin_cases e <;>
  · simp only [b65q_fibreC, b65q_PC, b65q_fibreValue, b65q_fibreCoeff, Fin.sum_univ_succ,
      Fin.sum_univ_zero]
    norm_num
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_div₀, map_ofNat,
      map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    ring

theorem b65q_fibreC_coeff (e : Fin 2) (n : ℕ) :
    (b65q_fibreC e).coeff n = if h : n < 7 then ((b65q_fibreCoeff e ⟨n, h⟩ : ℚ) : ℂ) else 0 := by
  rw [b65q_fibreC_eq, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; · simp
      intro hn; exact hb (Fin.ext hn.symm)
    · simp
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; · simp
    intro hn; exact h (hn ▸ b.2)

theorem b65q_fibreC_natDegree (e : Fin 2) : (b65q_fibreC e).natDegree = 6 := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [b65q_fibreC_coeff]
    have hn' : 6 < n := by exact_mod_cast hn
    by_cases h7 : n < 7
    · omega
    · simp [h7]
  · apply le_natDegree_of_ne_zero
    rw [b65q_fibreC_coeff]
    fin_cases e <;> norm_num [b65q_fibreCoeff]

theorem b65q_fibreC_monic (e : Fin 2) : (b65q_fibreC e).Monic := by
  rw [Monic, leadingCoeff, b65q_fibreC_natDegree, b65q_fibreC_coeff]
  fin_cases e <;> norm_num [b65q_fibreCoeff]

/-- A monic polynomial of positive degree is determined, among monic polynomials of its degree,
by its logarithmic derivative. -/
theorem b65q_eq_of_logDeriv {P Q : ℂ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hd : Q.natDegree = P.natDegree) (hn : 0 < P.natDegree)
    (h : Q.derivative * P = P.derivative * Q) : Q = P := by
  by_contra hne
  set R := Q - P with hR
  have hR0 : R ≠ 0 := sub_ne_zero.mpr hne
  have hRd : R.natDegree < P.natDegree := by
    have hdeg : Q.degree = P.degree := by
      rw [degree_eq_natDegree hQ.ne_zero, degree_eq_natDegree hP.ne_zero, hd]
    have := degree_sub_lt_left hdeg hQ.ne_zero (by rw [hQ.leadingCoeff, hP.leadingCoeff])
    rw [degree_eq_natDegree hQ.ne_zero, hd] at this
    exact (natDegree_lt_iff_degree_lt hR0).2 this
  have hRe : R.derivative * P = P.derivative * R := by
    rw [hR, derivative_sub, sub_mul, mul_sub, h]
  set d := R.natDegree
  set n := P.natDegree
  have hlc : R.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hR0
  have hPd : P.derivative.natDegree ≤ n - 1 := by
    have := natDegree_derivative_le P; omega
  have h2 : (P.derivative * R).coeff (n - 1 + d) = (n : ℂ) * R.coeff d := by
    rw [coeff_mul_add_eq_of_natDegree_le hPd le_rfl, coeff_derivative, Nat.sub_add_cancel hn, hP.coeff_natDegree]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hR' : R.derivative = 0 := by
      rw [eq_C_of_natDegree_eq_zero hd0, derivative_C]
    rw [hR', zero_mul] at hRe
    have := congrArg (fun f : ℂ[X] ↦ f.coeff (n - 1 + d)) hRe
    simp only [coeff_zero] at this
    rw [h2] at this
    exact hlc (by
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_eq_zero.mp this.symm).resolve_left hn0)
  · have hRd' : R.derivative.natDegree ≤ d - 1 := by
      have := natDegree_derivative_le R; omega
    have h1 : (R.derivative * P).coeff (d - 1 + n) = (d : ℂ) * R.coeff d := by
      rw [coeff_mul_add_eq_of_natDegree_le hRd' le_rfl, coeff_derivative, Nat.sub_add_cancel hdpos,
        hP.coeff_natDegree]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := congrArg (fun f : ℂ[X] ↦ f.coeff (d - 1 + n)) hRe
    rw [h1, show d - 1 + n = n - 1 + d by omega, h2] at this
    have hdn : (d : ℂ) ≠ n := by exact_mod_cast hRd.ne
    exact hlc (by
      have : ((d : ℂ) - n) * R.coeff d = 0 := by rw [sub_mul, this, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hdn))


theorem b65q_PC_ne_zero (ε : ℂ) : b65q_PC ε ≠ 0 := by
  intro h0
  have := congrArg (fun f : ℂ[X] ↦ f.eval 1) h0
  norm_num [b65q_PC] at this

theorem b65q_fibreC_eval (e : Fin 2) (s : ℂ) :
    (b65q_fibreC e).eval s = (1 - ((b65q_fibreValue e : ℤ) : ℂ))⁻¹ * b65r_P ((b65q_fibreValue e : ℤ) : ℂ) s := by
  simp [b65q_fibreC, b65q_PC_eval]

theorem b65q_fibreC_ratio (e : Fin 2) (s : ℂ) :
    (b65q_fibreC e).derivative.eval s / (b65q_fibreC e).eval s =
      (b65q_PC ((b65q_fibreValue e : ℤ) : ℂ)).derivative.eval s /
        (b65q_PC ((b65q_fibreValue e : ℤ) : ℂ)).eval s := by
  have hc : (1 - ((b65q_fibreValue e : ℤ) : ℂ))⁻¹ ≠ 0 := by
    fin_cases e <;> norm_num [b65q_fibreValue]
  simp only [b65q_fibreC, derivative_C_mul, eval_C_mul]
  rw [mul_div_mul_left _ _ hc]

theorem b65q_fibreSet_card (e : Fin 2) : (b65q_fibreSet e).card = 6 := by
  fin_cases e <;> decide

/-- **The labelled poles over each fibre are the roots of the fibre polynomial.** -/
theorem b65q_fibre_prod {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) :
    ∏ x ∈ b65q_fibreSet e, (X - C (p x)) = b65q_fibreC e := by
  have hQm : (∏ x ∈ b65q_fibreSet e, (X - C (p x))).Monic :=
    monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _
  have hQd : (∏ x ∈ b65q_fibreSet e, (X - C (p x))).natDegree = 6 := by
    rw [natDegree_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _]
    simp [b65q_fibreSet_card]
  refine b65q_eq_of_logDeriv (b65q_fibreC_monic e) hQm (by rw [hQd, b65q_fibreC_natDegree])
    (by rw [b65q_fibreC_natDegree]; norm_num) ?_
  apply eq_of_infinite_eval_eq
  set T : Set ℂ := ({0, 3, 1, -2} : Set ℂ) ∪ {z | IsRoot (b65q_PC 5) z} ∪
    {z | IsRoot (b65q_PC (-7)) z} ∪ Set.range p
  have hT : T.Finite := by
    refine ((((Set.toFinite _).union ?_).union ?_).union (Set.finite_range p))
    · exact finite_setOf_isRoot (b65q_PC_ne_zero 5)
    · exact finite_setOf_isRoot (b65q_PC_ne_zero (-7))
  refine hT.infinite_compl.mono ?_
  intro s hs
  simp only [T, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Set.mem_range, IsRoot.def, not_or, not_exists] at hs
  obtain ⟨⟨⟨⟨h0, h3, h1, h2⟩, h5⟩, h7⟩, hp⟩ := hs
  have hreg : s ∈ b65s_regular := by
    refine ⟨h0, h3, h1, h2, ?_, ?_⟩
    · rw [← b65q_PC_eval]; exact h5
    · rw [← b65q_PC_eval]; push_cast; exact h7
  have hlog := b65q_base_logDeriv O s hreg
  have hsum : (∑ x ∈ b65q_fibreSet e, (s - p x)⁻¹) =
      (b65q_fibreC e).derivative.eval s / (b65q_fibreC e).eval s := by
    rw [b65q_fibreC_ratio]
    fin_cases e
    · simpa [b65q_fibreValue] using hlog.1
    · simpa [b65q_fibreValue] using hlog.2
  have hne : ∀ x, s - p x ≠ 0 := fun x ↦ sub_ne_zero.mpr fun h ↦ hp x h.symm
  have hQs : (∏ x ∈ b65q_fibreSet e, (X - C (p x))).eval s ≠ 0 := by
    rw [eval_prod]; exact Finset.prod_ne_zero_iff.mpr fun x _ ↦ by simpa using hne x
  have hPs : (b65q_fibreC e).eval s ≠ 0 := by
    simp only [b65q_fibreC, eval_C_mul]
    fin_cases e
    · exact mul_ne_zero (by norm_num [b65q_fibreValue]) (by simpa [b65q_fibreValue] using h5)
    · exact mul_ne_zero (by norm_num [b65q_fibreValue]) (by simpa [b65q_fibreValue] using h7)
  have hQ' : (∏ x ∈ b65q_fibreSet e, (X - C (p x))).derivative.eval s /
      (∏ x ∈ b65q_fibreSet e, (X - C (p x))).eval s = ∑ x ∈ b65q_fibreSet e, (s - p x)⁻¹ := by
    rw [derivative_prod_finset, eval_finset_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [derivative_X_sub_C, mul_one, ← Finset.mul_prod_erase _ _ hx]
    simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    have : ∏ j ∈ (b65q_fibreSet e).erase x, (s - p j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ hne j
    field_simp
  have key := hQ'.trans hsum
  rw [div_eq_div_iff hQs hPs] at key
  simp only [Set.mem_setOf_eq, eval_mul]
  linear_combination key


/-- **Newton's identities** for a product of linear factors, from its derivative. -/
theorem b65q_newton {ι : Type*} [DecidableEq ι] (F : Finset ι) (y : ι → ℂ) (n : ℕ) :
    (∏ x ∈ F, (X - C (y x))).coeff (n + 1) * ((n : ℂ) + 1) =
      ∑ j ∈ Finset.range (F.card - n),
        (∏ x ∈ F, (X - C (y x))).coeff (n + 1 + j) * ∑ x ∈ F, y x ^ j := by
  set Q := ∏ x ∈ F, (X - C (y x)) with hQ
  have hdeg : Q.natDegree = F.card := by
    rw [hQ, natDegree_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _]; simp
  have hder : Q.derivative = ∑ x ∈ F, Q /ₘ (X - C (y x)) := by
    rw [hQ, derivative_prod_finset]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [derivative_X_sub_C, mul_one, ← Finset.mul_prod_erase _ _ hx,
      mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
  have h1 := congrArg (fun f : ℂ[X] ↦ f.coeff n) hder
  simp only [coeff_derivative, finsetSum_coeff, coeff_divByMonic_X_sub_C, hdeg] at h1
  rw [h1, Finset.sum_comm]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show F.card + 1 - (n + 1) = F.card - n by omega]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [show n + 1 + j - (n + 1) = j by omega, mul_comm]

/-- Power sums `Σ t^v`, `v ≤ 5`, of the six roots of `P₅` (row `0`) and of `P₋₇` (row `1`):
the traces of the powers of the companion matrices. -/
def b65q_psumQ : Fin 2 → Fin 6 → ℚ :=
  ![![6, -27/4, 1281/16, -44583/64, 1593249/256, -56573847/1024],
    ![6, -9/8, -447/64, 41919/512, -617727/4096, -11953089/32768]]

theorem b65q_psum {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (v : Fin 6) :
    ∑ x ∈ b65q_fibreSet e, p x ^ (v : ℕ) = ((b65q_psumQ e v : ℚ) : ℂ) := by
  have N : ∀ n, (b65q_fibreC e).coeff (n + 1) * ((n : ℂ) + 1) =
      ∑ j ∈ Finset.range (6 - n), (b65q_fibreC e).coeff (n + 1 + j) *
        ∑ x ∈ b65q_fibreSet e, p x ^ j := by
    intro n
    have := b65q_newton (b65q_fibreSet e) p n
    rwa [b65q_fibre_prod O e, b65q_fibreSet_card] at this
  set π : ℕ → ℂ := fun j ↦ ∑ x ∈ b65q_fibreSet e, p x ^ j with hπ
  have N5 := N 5
  have N4 := N 4
  have N3 := N 3
  have N2 := N 2
  have N1 := N 1
  have N0 := N 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, b65q_fibreC_coeff, pow_zero,
    Finset.sum_const, b65q_fibreSet_card, nsmul_eq_mul, mul_one, pow_one] at N5 N4 N3 N2 N1 N0
  fin_cases e <;> norm_num [b65q_fibreCoeff] at N5 N4 N3 N2 N1 N0 <;>
  · have h1 := N4
    have h2 := N3
    have h3 := N2
    have h4 := N1
    have h5 := N0
    have e1 : ∑ x ∈ b65q_fibreSet _, p x = _ := eq_sub_of_add_eq' h1.symm
    rw [e1] at h2 h3 h4 h5
    have e2 : ∑ x ∈ b65q_fibreSet _, p x ^ 2 = _ := eq_sub_of_add_eq' h2.symm
    rw [e2] at h3 h4 h5
    have e3 : ∑ x ∈ b65q_fibreSet _, p x ^ 3 = _ := eq_sub_of_add_eq' h3.symm
    rw [e3] at h4 h5
    have e4 : ∑ x ∈ b65q_fibreSet _, p x ^ 4 = _ := eq_sub_of_add_eq' h4.symm
    rw [e4] at h5
    have e5 : ∑ x ∈ b65q_fibreSet _, p x ^ 5 = _ := eq_sub_of_add_eq' h5.symm
    fin_cases v <;> simp only [b65q_psumQ] <;> norm_num [e1, e2, e3, e4, e5, b65q_fibreSet_card]


theorem b65q_root_explicit_0 (r : ℂ) : (b65q_fibreC 0).eval r =
    r ^ 6 + 27/4 * r ^ 5 - 69/4 * r ^ 4 + 53/4 * r ^ 3 - 51/4 * r ^ 2 + 15 * r - 10 := by
  rw [b65q_fibreC_eq]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Fin.sum_univ_succ,
    Fin.sum_univ_zero, b65q_fibreCoeff]
  norm_num
  ring

theorem b65q_root_explicit_1 (r : ℂ) : (b65q_fibreC 1).eval r =
    r ^ 6 + 9/8 * r ^ 5 + 33/8 * r ^ 4 - 185/8 * r ^ 3 + 123/8 * r ^ 2 + 21/2 * r - 7 := by
  rw [b65q_fibreC_eq]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Fin.sum_univ_succ,
    Fin.sum_univ_zero, b65q_fibreCoeff]
  norm_num
  ring

theorem b65q_fibre_root {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) {x : Fin 12}
    (hx : x ∈ b65q_fibreSet e) : (b65q_fibreC e).eval (p x) = 0 := by
  rw [← b65q_fibre_prod O e, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- A function agreeing with a polynomial of degree at most five on the roots of a fibre
polynomial sums, over the labels of that fibre, to the corresponding combination of power
sums. -/
theorem b65q_fibre_reduce {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (g : ℂ → ℂ)
    (h : Fin 6 → ℚ)
    (hg : ∀ r : ℂ, (b65q_fibreC e).eval r = 0 → g r = ∑ i : Fin 6, ((h i : ℚ) : ℂ) * r ^ (i : ℕ)) :
    ∑ x ∈ b65q_fibreSet e, g (p x) = ((∑ i : Fin 6, h i * b65q_psumQ e i : ℚ) : ℂ) := by
  rw [Finset.sum_congr rfl fun x hx ↦ hg (p x) (b65q_fibre_root O e hx), Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_sum, b65q_psum O e i]

theorem b65q_invSum_0_0_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 0) ^ 1)⁻¹ = (((3/2) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 0) ^ 1)⁻¹)
    ![(3/2), (-51/40), (53/40), (-69/40), (27/40), (1/10)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/10) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_0_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 0) ^ 2)⁻¹ = (((-3/10) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 0) ^ 2)⁻¹)
    ![(39/40), (-47/80), (21/80), (-153/80), (89/80), (3/20)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/10) * r ^ 0 + (3/20) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_0_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 0) ^ 3)⁻¹ = (((129/80) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 0) ^ 3)⁻¹)
    ![(7/8), (-1569/1600), (-993/1600), (-911/1600), (1293/1600), (39/400)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/10) * r ^ 0 + (3/20) * r ^ 1 + (39/400) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_0_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 0) ^ 4)⁻¹ = (((-1689/800) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 0) ^ 4)⁻¹)
    ![(531/1600), (-1389/800), (59/100), (-561/800), (1101/1600), (7/80)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/10) * r ^ 0 + (3/20) * r ^ 1 + (39/400) * r ^ 2 + (7/80) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_0_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 0) ^ 5)⁻¹ = (((-3093/640) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 0) ^ 5)⁻¹)
    ![(-3963/3200), (10679/64000), (-16737/64000), (7401/64000), (19937/64000), (531/16000)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/10) * r ^ 0 + (3/20) * r ^ 1 + (39/400) * r ^ 2 + (7/80) * r ^ 3 + (531/16000) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_1_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 1) ^ 1)⁻¹ = (((-21/10) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 1) ^ 1)⁻¹)
    ![(-42/125), (-27/250), (-197/5000), (-6/625), (-39/5000), (-1/1250)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1/1250) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_1_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 1) ^ 2)⁻¹ = (((87/100) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 1) ^ 2)⁻¹)
    ![(147/1250), (167/2500), (2127/50000), (249/25000), (779/50000), (21/12500)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-73/12500) * r ^ 0 + (21/12500) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_1_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 1) ^ 3)⁻¹ = (((-399/1000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 1) ^ 3)⁻¹)
    ![(-289/6250), (-339/12500), (-8049/250000), (-1181/250000), (-591/31250), (-33/15625)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1553/62500) * r ^ 0 + (897/62500) * r ^ 1 + (-33/15625) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_1_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 1) ^ 4)⁻¹ = (((399/2000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 1) ^ 4)⁻¹)
    ![(279/12500), (153/25000), (10789/500000), (-6/15625), (1809/100000), (259/125000)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-10099/125000) * r ^ 0 + (8787/125000) * r ^ 1 + (-519/25000) * r ^ 2 + (259/125000) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_1_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 1) ^ 5)⁻¹ = (((-10761/100000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 1) ^ 5)⁻¹)
    ![(-16611/1250000), (5759/2500000), (-694101/50000000), (40629/12500000), (-751787/50000000), (-21933/12500000)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-2786473/12500000) * r ^ 0 + (405933/1562500) * r ^ 1 + (-721941/6250000) * r ^ 2 + (36137/1562500) * r ^ 3 + (-21933/12500000) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_2_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 2) ^ 1)⁻¹ = (((0) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 2) ^ 1)⁻¹)
    ![(3/2), (-9/4), (15/16), (-19/8), (31/16), (1/4)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/4) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_2_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 2) ^ 2)⁻¹ = (((3) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 2) ^ 2)⁻¹)
    ![(-3/2), (3/4), (-3/16), (35/16), (1/4), (0)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/4) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_2_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 2) ^ 3)⁻¹ = (((381/16) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 2) ^ 3)⁻¹)
    ![(21/4), (-9/8), (123/32), (-53/16), (93/32), (3/8)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((5/8) * r ^ 0 + (-3/4) * r ^ 1 + (3/8) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_2_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 2) ^ 4)⁻¹ = (((36) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 2) ^ 4)⁻¹)
    ![(467/32), (-899/64), (1897/256), (-1993/128), (4033/256), (127/64)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-87/64) * r ^ 0 + (333/64) * r ^ 1 + (-357/64) * r ^ 2 + (127/64) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_2_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 2) ^ 5)⁻¹ = (((2415/32) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 2) ^ 5)⁻¹)
    ![(343/32), (-845/64), (2985/256), (-1615/256), (2765/128), (81/32)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((75/64) * r ^ 0 + (-315/64) * r ^ 1 + (615/64) * r ^ 2 + (-521/64) * r ^ 3 + (81/32) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_3_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 3) ^ 1)⁻¹ = (((9/5) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 3) ^ 1)⁻¹)
    ![(123/250), (-117/500), (267/2500), (-107/2500), (19/2500), (1/625)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/625) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_3_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 3) ^ 2)⁻¹ = (((33/50) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 3) ^ 2)⁻¹)
    ![(579/2500), (-132/625), (879/6250), (-227/3125), (191/12500), (9/3125)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((23/3125) * r ^ 0 + (9/3125) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_3_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 3) ^ 3)⁻¹ = (((3/25) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 3) ^ 3)⁻¹)
    ![(501/5000), (-1323/10000), (5829/50000), (-3697/50000), (177/10000), (39/12500)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((62/3125) * r ^ 0 + (48/3125) * r ^ 1 + (39/12500) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_3_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 3) ^ 4)⁻¹ = (((-207/5000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 3) ^ 4)⁻¹)
    ![(9313/250000), (-2047/31250), (46663/625000), (-17899/312500), (19157/1250000), (803/312500)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((3156/78125) * r ^ 0 + (3609/78125) * r ^ 1 + (5793/312500) * r ^ 2 + (803/312500) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_0_3_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 0, ((p x - b65p_fixedPole 3) ^ 5)⁻¹ = (((-417/6250) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 0 (fun r ↦ ((r - b65p_fixedPole 3) ^ 5)⁻¹)
    ![(24803/2500000), (-123277/5000000), (963987/25000000), (-909607/25000000), (270979/25000000), (10881/6250000)] fun r hr ↦ by
      rw [b65q_root_explicit_0] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((26661/390625) * r ^ 0 + (39807/390625) * r ^ 1 + (94251/1562500) * r ^ 2 + (25777/1562500) * r ^ 3 + (10881/6250000) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_0_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 0) ^ 1)⁻¹ = (((3/2) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 0) ^ 1)⁻¹)
    ![(3/2), (123/56), (-185/56), (33/56), (9/56), (1/7)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/7) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_0_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 0) ^ 2)⁻¹ = (((93/14) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 0) ^ 2)⁻¹)
    ![(249/56), (-1/112), (-489/112), (117/112), (43/112), (3/14)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/7) * r ^ 0 + (3/14) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_0_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 0) ^ 3)⁻¹ = (((375/112) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 0) ^ 3)⁻¹)
    ![(373/56), (16935/3136), (-42789/3136), (9421/3136), (2913/3136), (249/392)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/7) * r ^ 0 + (3/14) * r ^ 1 + (249/392) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_0_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 0) ^ 4)⁻¹ = (((26679/1568) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 0) ^ 4)⁻¹)
    ![(48267/3136), (1545/1568), (-19), (7611/1568), (5349/3136), (373/392)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/7) * r ^ 0 + (3/14) * r ^ 1 + (249/392) * r ^ 2 + (373/392) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_0_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 0) ^ 5)⁻¹ = (((79143/6272) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 0) ^ 5)⁻¹)
    ![(150981/6272), (2600137/175616), (-8076963/175616), (1892355/175616), (601507/175616), (48267/21952)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 0 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 0 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((1/7) * r ^ 0 + (3/14) * r ^ 1 + (249/392) * r ^ 2 + (373/392) * r ^ 3 + (48267/21952) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_1_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 1) ^ 1)⁻¹ = (((-21/10) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 1) ^ 1)⁻¹)
    ![(-42/125), (-27/250), (-211/7000), (-33/1750), (-33/7000), (-1/875)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1/875) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_1_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 1) ^ 2)⁻¹ = (((87/100) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 1) ^ 2)⁻¹)
    ![(147/1250), (167/2500), (1401/70000), (1101/35000), (613/70000), (3/1250)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-73/8750) * r ^ 0 + (3/1250) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_1_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 1) ^ 3)⁻¹ = (((-399/1000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 1) ^ 3)⁻¹)
    ![(-289/6250), (-339/12500), (-87/350000), (-11839/350000), (-879/87500), (-66/21875)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1553/43750) * r ^ 0 + (897/43750) * r ^ 1 + (-66/21875) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_1_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 1) ^ 4)⁻¹ = (((13101/70000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 1) ^ 4)⁻¹)
    ![(279/12500), (153/25000), (-9133/700000), (1041/35000), (1287/140000), (37/12500)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-10099/87500) * r ^ 0 + (8787/87500) * r ^ 1 + (-519/17500) * r ^ 2 + (37/12500) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_1_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 1) ^ 5)⁻¹ = (((-59847/700000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 1) ^ 5)⁻¹)
    ![(-23241/1750000), (1147/500000), (1758327/98000000), (-284547/12250000), (-721799/98000000), (-30663/12250000)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 1 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 1 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-3897563/12250000) * r ^ 0 + (567723/1531250) * r ^ 1 + (-1009551/6125000) * r ^ 2 + (50527/1531250) * r ^ 3 + (-30663/12250000) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_2_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 2) ^ 1)⁻¹ = (((0) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 2) ^ 1)⁻¹)
    ![(-9/2), (3/4), (135/16), (-25/8), (-17/16), (-1/2)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1/2) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_2_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 2) ^ 2)⁻¹ = (((3) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 2) ^ 2)⁻¹)
    ![(9/2), (15/4), (-75/16), (-25/16), (-1/2), (0)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-1/2) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_2_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 2) ^ 3)⁻¹ = (((-591/16) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 2) ^ 3)⁻¹)
    ![(-39/4), (-45/8), (339/32), (-83/16), (-51/32), (-3/4)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-5/4) * r ^ 0 + (3/2) * r ^ 1 + (-3/4) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_2_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 2) ^ 4)⁻¹ = (((-45) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 2) ^ 4)⁻¹)
    ![(1691/32), (-395/64), (-28523/256), (4625/128), (3157/256), (197/32)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-237/32) * r ^ 0 + (639/32) * r ^ 1 + (-615/32) * r ^ 2 + (197/32) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_2_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 2) ^ 5)⁻¹ = (((-3525/32) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 2) ^ 5)⁻¹)
    ![(-557/32), (-4121/64), (-7887/256), (12833/256), (2165/128), (81/16)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 2 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 2 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-75/32) * r ^ 0 + (-9/32) * r ^ 1 + (357/32) * r ^ 2 + (-451/32) * r ^ 3 + (81/16) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_3_1 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 3) ^ 1)⁻¹ = (((9/5) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 3) ^ 1)⁻¹)
    ![(639/1250), (-681/2500), (279/2500), (-47/2500), (7/2500), (-2/625)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-2/625) * r ^ 0) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_3_2 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 3) ^ 2)⁻¹ = (((33/50) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 3) ^ 2)⁻¹)
    ![(3447/12500), (-951/3125), (1023/6250), (-77/3125), (23/12500), (-18/3125)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-46/3125) * r ^ 0 + (-18/3125) * r ^ 1) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_3_3 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 3) ^ 3)⁻¹ = (((318/625) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 3) ^ 3)⁻¹)
    ![(3993/25000), (-13239/50000), (8313/50000), (-233/10000), (-3/10000), (-39/6250)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-124/3125) * r ^ 0 + (-96/3125) * r ^ 1 + (-39/6250) * r ^ 2) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_3_4 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 3) ^ 4)⁻¹ = (((9333/25000) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 3) ^ 4)⁻¹)
    ![(620617/6250000), (-82499/390625), (456353/3125000), (-7988/390625), (-8627/6250000), (-4339/781250)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-32856/390625) * r ^ 0 + (-38034/390625) * r ^ 1 + (-30909/781250) * r ^ 2 + (-4339/781250) * r ^ 3) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

theorem b65q_invSum_1_3_5 {p : Fin 12 → ℂ} (O : b65p_Outputs p) :
    ∑ x ∈ b65q_fibreSet 1, ((p x - b65p_fixedPole 3) ^ 5)⁻¹ = (((3081/12500) : ℚ) : ℂ) := by
  have := b65q_fibre_reduce O 1 (fun r ↦ ((r - b65p_fixedPole 3) ^ 5)⁻¹)
    ![(4100627/62500000), (-20293093/125000000), (14891547/125000000), (-2132951/125000000), (-195469/125000000), (-71253/15625000)] fun r hr ↦ by
      rw [b65q_root_explicit_1] at hr
      have hne : r - b65p_fixedPole 3 ≠ 0 := by
        intro h0
        rw [show r = b65p_fixedPole 3 by linear_combination h0] at hr
        norm_num [b65p_fixedPole] at hr
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hne)]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedPole]
      norm_num
      linear_combination ((-306786/1953125) * r ^ 0 + (-475182/1953125) * r ^ 1 + (-582063/3906250) * r ^ 2 + (-164201/3906250) * r ^ 3 + (-71253/15625000) * r ^ 4) * hr
  rw [this]
  norm_num [b65q_psumQ, Fin.sum_univ_succ]

/-- Inverse power sums `Σ_t (t − a)^{−m}`, `m = 1 … 5`, over the roots of `P₅` (row `0`) and
`P₋₇` (row `1`), about the fixed poles `a = 0, 3, 1, −2`. -/
def b65q_invQ : Fin 2 → Fin 4 → Fin 5 → ℚ :=
  ![![![(3/2), (-3/10), (129/80), (-1689/800), (-3093/640)], ![(-21/10), (87/100), (-399/1000), (399/2000), (-10761/100000)], ![(0), (3), (381/16), (36), (2415/32)], ![(9/5), (33/50), (3/25), (-207/5000), (-417/6250)]],
    ![![(3/2), (93/14), (375/112), (26679/1568), (79143/6272)], ![(-21/10), (87/100), (-399/1000), (13101/70000), (-59847/700000)], ![(0), (3), (-591/16), (-45), (-3525/32)], ![(9/5), (33/50), (318/625), (9333/25000), (3081/12500)]]]

theorem b65q_invSum {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (k : Fin 4) (m : Fin 5) :
    ∑ x ∈ b65q_fibreSet e, ((p x - b65p_fixedPole k) ^ (m.val + 1))⁻¹ =
      ((b65q_invQ e k m : ℚ) : ℂ) := by
  fin_cases e <;> fin_cases k <;> fin_cases m
  · simpa [b65q_invQ] using b65q_invSum_0_0_1 O
  · simpa [b65q_invQ] using b65q_invSum_0_0_2 O
  · simpa [b65q_invQ] using b65q_invSum_0_0_3 O
  · simpa [b65q_invQ] using b65q_invSum_0_0_4 O
  · simpa [b65q_invQ] using b65q_invSum_0_0_5 O
  · simpa [b65q_invQ] using b65q_invSum_0_1_1 O
  · simpa [b65q_invQ] using b65q_invSum_0_1_2 O
  · simpa [b65q_invQ] using b65q_invSum_0_1_3 O
  · simpa [b65q_invQ] using b65q_invSum_0_1_4 O
  · simpa [b65q_invQ] using b65q_invSum_0_1_5 O
  · simpa [b65q_invQ] using b65q_invSum_0_2_1 O
  · simpa [b65q_invQ] using b65q_invSum_0_2_2 O
  · simpa [b65q_invQ] using b65q_invSum_0_2_3 O
  · simpa [b65q_invQ] using b65q_invSum_0_2_4 O
  · simpa [b65q_invQ] using b65q_invSum_0_2_5 O
  · simpa [b65q_invQ] using b65q_invSum_0_3_1 O
  · simpa [b65q_invQ] using b65q_invSum_0_3_2 O
  · simpa [b65q_invQ] using b65q_invSum_0_3_3 O
  · simpa [b65q_invQ] using b65q_invSum_0_3_4 O
  · simpa [b65q_invQ] using b65q_invSum_0_3_5 O
  · simpa [b65q_invQ] using b65q_invSum_1_0_1 O
  · simpa [b65q_invQ] using b65q_invSum_1_0_2 O
  · simpa [b65q_invQ] using b65q_invSum_1_0_3 O
  · simpa [b65q_invQ] using b65q_invSum_1_0_4 O
  · simpa [b65q_invQ] using b65q_invSum_1_0_5 O
  · simpa [b65q_invQ] using b65q_invSum_1_1_1 O
  · simpa [b65q_invQ] using b65q_invSum_1_1_2 O
  · simpa [b65q_invQ] using b65q_invSum_1_1_3 O
  · simpa [b65q_invQ] using b65q_invSum_1_1_4 O
  · simpa [b65q_invQ] using b65q_invSum_1_1_5 O
  · simpa [b65q_invQ] using b65q_invSum_1_2_1 O
  · simpa [b65q_invQ] using b65q_invSum_1_2_2 O
  · simpa [b65q_invQ] using b65q_invSum_1_2_3 O
  · simpa [b65q_invQ] using b65q_invSum_1_2_4 O
  · simpa [b65q_invQ] using b65q_invSum_1_2_5 O
  · simpa [b65q_invQ] using b65q_invSum_1_3_1 O
  · simpa [b65q_invQ] using b65q_invSum_1_3_2 O
  · simpa [b65q_invQ] using b65q_invSum_1_3_3 O
  · simpa [b65q_invQ] using b65q_invSum_1_3_4 O
  · simpa [b65q_invQ] using b65q_invSum_1_3_5 O

theorem b65q_fixedPole_cast (k : Fin 4) : b65p_fixedPole k = ((b65k_fixed k : ℚ) : ℂ) := by
  fin_cases k <;> norm_num [b65p_fixedPole, b65k_fixed]

theorem b65q_fibre_ne_fixed {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (k : Fin 4)
    {x : Fin 12} (hx : x ∈ b65q_fibreSet e) : p x - b65p_fixedPole k ≠ 0 := by
  intro h0
  have hr := b65q_fibre_root O e hx
  rw [show p x = b65p_fixedPole k by linear_combination h0] at hr
  fin_cases e <;> fin_cases k <;>
    norm_num [b65q_root_explicit_0, b65q_root_explicit_1, b65p_fixedPole] at hr

/-- Mixed sums `Σ_t t^v (t − a)^{−m}` over the roots of a fibre polynomial, by the recursion
`t^{v+1}(t − a)^{−m−1} = t^v (t − a)^{−m} + a t^v (t − a)^{−m−1}`. -/
def b65q_DQ (e : Fin 2) (k : Fin 4) : ℕ → ℕ → ℚ
  | 0, v => if h : v < 6 then b65q_psumQ e ⟨v, h⟩ else 0
  | m + 1, 0 => if h : m < 5 then b65q_invQ e k ⟨m, h⟩ else 0
  | m + 1, v + 1 => b65q_DQ e k m v + b65k_fixed k * b65q_DQ e k (m + 1) v

theorem b65q_DQ_sum {p : Fin 12 → ℂ} (O : b65p_Outputs p) (e : Fin 2) (k : Fin 4) :
    ∀ v m : ℕ, v ≤ 5 → m ≤ 5 →
      ∑ x ∈ b65q_fibreSet e, p x ^ v * ((p x - b65p_fixedPole k) ^ m)⁻¹ =
        ((b65q_DQ e k m v : ℚ) : ℂ) := by
  intro v
  induction v with
  | zero =>
    intro m _ hm
    rcases m with _ | m
    · simpa [b65q_DQ] using b65q_psum O e 0
    · simpa [b65q_DQ, show m < 5 by omega] using b65q_invSum O e k ⟨m, by omega⟩
  | succ v ih =>
    intro m hv hm
    rcases m with _ | m
    · simpa [b65q_DQ, show v + 1 < 6 by omega] using b65q_psum O e ⟨v + 1, by omega⟩
    · have h1 := ih m (by omega) (by omega)
      have h2 := ih (m + 1) (by omega) hm
      simp only [b65q_DQ]
      push_cast
      rw [← h1, ← h2, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hne := b65q_fibre_ne_fixed O e k hx
      rw [← b65q_fixedPole_cast]
      field_simp
      ring

end HodgeLean.Foundations.Program
