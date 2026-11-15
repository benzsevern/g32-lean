import HodgeLean.Foundations.MeyerRationalDefs

/-! # Proof obligations for rational diagonal normalization -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

theorem diagonal_signs_aux (n : ℕ) (w : Fin n → ℚ) :
    ((∃ x, 0 < QuadraticMap.weightedSumSquares ℚ w x) ∧
      (∃ x, QuadraticMap.weightedSumSquares ℚ w x < 0)) ↔
    ((∃ i, 0 < w i) ∧ (∃ i, w i < 0)) := by
  classical
  simp only [QuadraticMap.weightedSumSquares_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    constructor
    · by_contra! h
      have hz : (∑ i, w i * x i ^ 2) ≤ 0 :=
        Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (h i) (sq_nonneg _)
      exact (not_lt_of_ge hz) (by simpa [smul_eq_mul, pow_two] using hx)
    · by_contra! h
      have hz : 0 ≤ (∑ i, w i * y i ^ 2) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)
      exact (not_lt_of_ge hz) (by simpa [smul_eq_mul, pow_two] using hy)
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨⟨Pi.single i 1, ?_⟩, ⟨Pi.single j 1, ?_⟩⟩
    · simpa [Pi.single_apply, smul_eq_mul] using hi
    · simpa [Pi.single_apply, smul_eq_mul] using hj

theorem integral_model_aux (n : ℕ) (w : Fin n → ℚ)
    (hw : ∀ i, w i ≠ 0) (hp : ∃ i, 0 < w i) (hm : ∃ i, w i < 0) :
    ∃ (D : ℕ) (a : Fin n → ℤ), 0 < D ∧
      (∀ i, (a i : ℚ) = D * w i) ∧ (∀ i, a i ≠ 0) ∧
      (∃ i, 0 < a i) ∧ (∃ i, a i < 0) ∧
      ∀ x, integralDiagonal n a x = (D : ℚ) * QuadraticMap.weightedSumSquares ℚ w x := by
  classical
  let D := ∏ i, (w i).den
  let a : Fin n → ℤ := fun i => ((D / (w i).den : ℕ) : ℤ) * (w i).num
  have hD : 0 < D := Finset.prod_pos fun i _ => (w i).den_pos
  have hdiv (i : Fin n) : (w i).den ∣ D :=
    Finset.dvd_prod_of_mem (fun j => (w j).den) (Finset.mem_univ i)
  have hcoef (i : Fin n) : (a i : ℚ) = (D : ℚ) * w i := by
    rw [show w i = (w i).num / (w i).den by symm; exact (w i).num_div_den]
    simp only [a, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdiv i) (by exact_mod_cast (w i).den_nz)]
    field_simp
  refine ⟨D, a, hD, hcoef, ?_, ?_, ?_, ?_⟩
  · intro i hai
    apply hw i
    have h := hcoef i
    rw [hai, Int.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hD.ne')
  · obtain ⟨i, hi⟩ := hp
    refine ⟨i, ?_⟩
    exact_mod_cast (show (0 : ℚ) < (a i : ℚ) by rw [hcoef]; positivity)
  · obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_⟩
    exact_mod_cast (show ((a i : ℚ) < 0) by
      rw [hcoef]
      exact mul_neg_of_pos_of_neg (by exact_mod_cast hD) hi)
  · intro x
    simp only [integralDiagonal, QuadraticMap.weightedSumSquares_apply, hcoef,
      smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    funext i
    ring

theorem five_restriction_aux (n : ℕ) (hn : 5 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hp : ∃ i, 0 < a i) (hm : ∃ i, a i < 0) :
    ∃ (e : Fin 5 ↪ Fin n) (T : (Fin 5 → ℚ) →ₗ[ℚ] (Fin n → ℚ)),
      Function.Injective T ∧ (∀ x i, T x (e i) = x i) ∧
      (∀ x j, j ∉ Set.range e → T x j = 0) ∧
      (∃ i, 0 < a (e i)) ∧ (∃ i, a (e i) < 0) ∧
      ∀ x, integralDiagonal n a (T x) = integralDiagonal 5 (a ∘ e) x := by
  classical
  obtain ⟨ip, hip⟩ := hp
  obtain ⟨im, him⟩ := hm
  have hpne : ip ≠ im := by intro h; subst im; omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_superset_card_eq
    (s := {ip, im}) (n := 5) (by simp [hpne]) (by simpa using hn)
  let e : Fin 5 ↪ Fin n :=
    (Finset.equivFinOfCardEq hcard).symm.toEmbedding.trans (Function.Embedding.subtype _)
  let T : (Fin 5 → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun x j => if j ∈ Set.range e then x (Function.invFun e j) else 0
      map_add' := by
        intro x y
        funext j
        split <;> simp_all
      map_smul' := by
        intro c x
        funext j
        split <;> simp_all }
  have hTe (x : Fin 5 → ℚ) (i : Fin 5) : T x (e i) = x i := by
    change (if e i ∈ Set.range e then x (Function.invFun e (e i)) else 0) = x i
    rw [if_pos ⟨i, rfl⟩]
    rw [Function.leftInverse_invFun e.injective i]
  have hs_range : Set.range e = (s : Set (Fin n)) := by
    ext j
    simp only [Set.mem_range, Finset.mem_coe, e]
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.equivFinOfCardEq hcard).symm i |>.property
    · intro hj
      let z : s := ⟨j, hj⟩
      exact ⟨Finset.equivFinOfCardEq hcard z, by simp [z]⟩
  have hipr : ip ∈ Set.range e := by rw [hs_range]; exact hs (by simp)
  have himr : im ∈ Set.range e := by rw [hs_range]; exact hs (by simp)
  obtain ⟨iep, hep⟩ := hipr
  obtain ⟨iem, hem⟩ := himr
  refine ⟨e, T, ?_, hTe, ?_, ⟨iep, hep ▸ hip⟩, ⟨iem, hem ▸ him⟩, ?_⟩
  · intro x y hxy
    funext i
    rw [← hTe x i, ← hTe y i, hxy]
  · intro x j hj
    change (if j ∈ Set.range e then x (Function.invFun e j) else 0) = 0
    rw [if_neg hj]
  · intro x
    simp only [integralDiagonal, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    rw [← Finset.sum_subset (s₁ := Finset.univ.filter (· ∈ Set.range e))
      (s₂ := Finset.univ) (by simp) (by
        intro j _ hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hj' : j ∉ Set.range e := by simpa using hj
        rw [show T x j = 0 by
          change (if j ∈ Set.range e then x (Function.invFun e j) else 0) = 0
          rw [if_neg hj']]
        ring)]
    rw [← Finset.sum_bij (s := Finset.univ)
      (t := Finset.univ.filter (· ∈ Set.range e)) (fun i _ => e i)
      (fun _ _ => by simp)
      (fun i _ j _ hij => e.injective hij)
      (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨i, rfl⟩ := hj
        exact ⟨i, Finset.mem_univ _, rfl⟩)
      (fun i _ => by rw [hTe])]
    rfl

end HodgeLean.Foundations.MeyerRational
