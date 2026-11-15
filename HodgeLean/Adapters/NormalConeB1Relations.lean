import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Homogeneous relations and ideal powers -/

noncomputable section
namespace HodgeLean.Adapters

theorem a3b1_homogeneous_eval_mem_succ_pow
    {R σ : Type*} [CommRing R] (f : σ → R) (n : ℕ)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous n)
    (hc : ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) := by
  classical
  rw [p.as_sum, map_sum]
  apply Ideal.sum_mem
  intro d hd
  have hdn : d.degree = n := by
    simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (MvPolynomial.mem_support_iff.mp hd)
  have hmon : (MvPolynomial.monomial d (1 : R)).eval f ∈
      Ideal.span (Set.range f) ^ n := by
    apply (Ideal.mem_span_pow_iff_exists_isHomogeneous f _).mpr
    exact ⟨MvPolynomial.monomial d 1, MvPolynomial.isHomogeneous_monomial 1 hdn, rfl⟩
  rw [pow_succ']
  simpa only [MvPolynomial.eval_monomial, one_mul] using
    Ideal.mul_mem_mul (hc d) hmon

theorem a3b1_cancel_mod_ideal_powers
    {R σ : Type*} [CommRing R] (f : σ → R)
    (hc : ∀ (n : ℕ) (p : MvPolynomial σ R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
      ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (r : R) (hr : ∀ x, r * x ∈ Ideal.span (Set.range f) →
      x ∈ Ideal.span (Set.range f)) (n : ℕ) (x : R)
    (hx : r * x ∈ Ideal.span (Set.range f) ^ n) :
    x ∈ Ideal.span (Set.range f) ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hx' := ih x (Ideal.pow_le_pow_right (Nat.le_succ n) hx)
      obtain ⟨p, hp, hpe⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f x).mp hx'
      have hcp := hc n (MvPolynomial.C r * p) (hp.C_mul r) (by
        simpa [hpe] using hx)
      rw [← hpe]
      apply a3b1_homogeneous_eval_mem_succ_pow f n p hp
      intro d
      apply hr
      simpa only [MvPolynomial.coeff_C_mul] using hcp d

theorem a3b1_top_coefficient_eval_mem
    {R σ : Type*} [CommRing R] (f : σ → R) (r : R)
    (n m : ℕ) (hn : m ≤ n) (p : Polynomial (MvPolynomial σ R))
    (hp : ∀ i, (p.coeff i).IsHomogeneous (n - i))
    (hb : p.natDegree ≤ m)
    (he : p.eval₂ (MvPolynomial.eval f) r = 0) :
    (p.coeff m).eval f * r ^ m ∈ Ideal.span (Set.range f) ^ (n - m + 1) := by
  classical
  have hsum : (∑ i ∈ Finset.range m, (p.coeff i).eval f * r ^ i) ∈
      Ideal.span (Set.range f) ^ (n - m + 1) := by
    apply Ideal.sum_mem
    intro i hi
    have hpi : (p.coeff i).eval f ∈ Ideal.span (Set.range f) ^ (n - i) :=
      (Ideal.mem_span_pow_iff_exists_isHomogeneous f _).mpr ⟨p.coeff i, hp i, rfl⟩
    apply Ideal.mul_mem_right
    apply Ideal.pow_le_pow_right (show n - m + 1 ≤ n - i by
      have := Finset.mem_range.mp hi
      omega) hpi
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hb), Finset.sum_range_succ] at he
  rw [eq_neg_of_add_eq_zero_right he]
  exact neg_mem hsum

theorem a3b1_polynomial_relation_coeff_mem
    {R σ : Type*} [CommRing R] (f : σ → R)
    (hc : ∀ (n : ℕ) (p : MvPolynomial σ R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
      ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (r : R) (hr : ∀ x, r * x ∈ Ideal.span (Set.range f) →
      x ∈ Ideal.span (Set.range f))
    (m n : ℕ) (hn : m ≤ n) (p : Polynomial (MvPolynomial σ R))
    (hp : ∀ i, (p.coeff i).IsHomogeneous (n - i))
    (hb : p.natDegree ≤ m) (he : p.eval₂ (MvPolynomial.eval f) r = 0) :
    ∀ i d, (p.coeff i).coeff d ∈ Ideal.span (Set.range f) ⊔ Ideal.span {r} := by
  classical
  let J := Ideal.span (Set.range f)
  let K := J ⊔ Ideal.span {r}
  have hcancel (a k : ℕ) (x : R) (hx : x * r ^ k ∈ J ^ a) : x ∈ J ^ a := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        apply ih
        apply a3b1_cancel_mod_ideal_powers f hc r hr a (x * r ^ k)
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hx
  induction m generalizing n p with
  | zero =>
      have htop := a3b1_top_coefficient_eval_mem f r n 0 (Nat.zero_le n) p hp hb he
      simp only [pow_zero, mul_one, Nat.sub_zero] at htop
      intro i d
      by_cases hi : i = 0
      · subst i
        exact (show J ≤ K from le_sup_left) (hc n (p.coeff 0) (by simpa using hp 0) htop d)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
  | succ m ih =>
      have ht := hcancel (n - (m + 1) + 1) (m + 1) _
        (a3b1_top_coefficient_eval_mem f r n (m + 1) hn p hp hb he)
      have hL := hc (n - (m + 1)) (p.coeff (m + 1)) (hp _) ht
      obtain ⟨s, hs, hse⟩ :=
        (Ideal.mem_span_pow_iff_exists_isHomogeneous f _).mp ht
      have hdeg : n - (m + 1) + 1 = n - m := by omega
      rw [hdeg] at hs
      let q := p - Polynomial.monomial (m + 1) (p.coeff (m + 1)) +
        Polynomial.monomial m (MvPolynomial.C r * s)
      have hq (i : ℕ) : (q.coeff i).IsHomogeneous (n - i) := by
        dsimp [q]
        rw [Polynomial.coeff_add, Polynomial.coeff_sub]
        apply MvPolynomial.IsHomogeneous.add
        · apply (hp i).sub
          by_cases h : m + 1 = i
          · subst i
            simpa using hp (m + 1)
          · simp [Polynomial.coeff_monomial, h, MvPolynomial.isHomogeneous_zero]
        · by_cases h : m = i
          · subst i
            simpa using hs.C_mul r
          · simp [Polynomial.coeff_monomial, h, MvPolynomial.isHomogeneous_zero]
      have hqb : q.natDegree ≤ m := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro i hi
        dsimp [q]
        rw [Polynomial.coeff_add, Polynomial.coeff_sub]
        by_cases h : m + 1 = i
        · subst i
          simp [Polynomial.coeff_monomial]
        · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega : p.natDegree < i)
          simp [Polynomial.coeff_monomial, h, ne_of_lt hi, Ne.symm (ne_of_lt hi), hz]
      have hqe : q.eval₂ (MvPolynomial.eval f) r = 0 := by
        dsimp [q]
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_monomial,
          map_mul, MvPolynomial.eval_C, hse, he, pow_succ]
        ring
      have hqc := ih n (by omega) q hq hqb hqe
      intro i d
      have htop : ((Polynomial.monomial (m + 1) (p.coeff (m + 1))).coeff i).coeff d ∈ K := by
        by_cases h : m + 1 = i
        · simpa [Polynomial.coeff_monomial, h] using (show (p.coeff (m + 1)).coeff d ∈ K from (show J ≤ K from le_sup_left) (hL d))
        · simp [Polynomial.coeff_monomial, h, K]
      have hcorr : ((Polynomial.monomial m (MvPolynomial.C r * s)).coeff i).coeff d ∈ K := by
        by_cases h : m = i
        · simp only [Polynomial.coeff_monomial, if_pos h, MvPolynomial.coeff_C_mul]
          exact K.mul_mem_right _ ((show Ideal.span {r} ≤ K from le_sup_right)
            (Ideal.subset_span (Set.mem_singleton r)))
        · simp [Polynomial.coeff_monomial, h, K]
      have hmem := K.sub_mem (K.add_mem (hqc i d) htop) hcorr
      convert hmem using 1
      dsimp [q]
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, MvPolynomial.coeff_add,
        MvPolynomial.coeff_sub]
      ring

theorem a3b1_regular_append_cancel
    {R : Type*} [CommRing R] (rs : List R) (r : R)
    (h : RingTheory.Sequence.IsWeaklyRegular R (rs ++ [r]))
    (x : R) (hx : r * x ∈ Ideal.ofList rs) : x ∈ Ideal.ofList rs := by
  have hlast := (RingTheory.Sequence.isWeaklyRegular_append_iff R rs [r]).mp h |>.2
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hlast
  have hI : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    simp
  rw [hI] at hlast
  apply (Submodule.Quotient.mk_eq_zero (Ideal.ofList rs)).mp
  apply hlast
  change Submodule.Quotient.mk (r * x) = r • (0 : R ⧸ Ideal.ofList rs)
  rw [smul_zero]
  exact (Submodule.Quotient.mk_eq_zero (Ideal.ofList rs)).mpr hx

theorem a3b1_span_range_eq_ofList_reverse
    {R : Type*} [CommRing R] {N : ℕ} (f : Fin N → R) :
    Ideal.span (Set.range f) = Ideal.ofList (List.ofFn f).reverse := by
  unfold Ideal.ofList
  congr 1
  ext x
  simp

theorem a3b1_power_expression_with_ideal_coefficients
    {R σ : Type*} [CommRing R] (f : σ → R) (n : ℕ) (y : R)
    (hy : y ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∃ p : MvPolynomial σ R, p.IsHomogeneous n ∧ p.eval f = y ∧
      ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  rw [pow_succ'] at hy
  induction hy using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
      obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f b).mp hb
      refine ⟨MvPolynomial.C a * p, hp.C_mul a, by simp, ?_⟩
      intro d
      rw [MvPolynomial.coeff_C_mul]
      exact (Ideal.span (Set.range f)).mul_mem_right _ ha
  | add x hx y hy ihx ihy =>
      obtain ⟨p, hp, hpe, hpc⟩ := ihx
      obtain ⟨q, hq, hqe, hqc⟩ := ihy
      refine ⟨p + q, hp.add hq, by simp [hpe, hqe], ?_⟩
      intro d
      rw [MvPolynomial.coeff_add]
      exact add_mem (hpc d) (hqc d)

theorem a3b1_finSucc_zero_eval_coeff_mem
    {R : Type*} [CommRing R] {N : ℕ} (f : Fin (N + 1) → R)
    (hc : ∀ (n : ℕ) (p : MvPolynomial (Fin N) R), p.IsHomogeneous n →
      p.eval (fun i ↦ f i.succ) ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)) ^ (n + 1) →
      ∀ d, p.coeff d ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)))
    (hr : ∀ x, f 0 * x ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)) →
      x ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)))
    (n : ℕ) (p : MvPolynomial (Fin (N + 1)) R)
    (hp : p.IsHomogeneous n) (he : p.eval f = 0) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  let P := MvPolynomial.finSuccEquiv R N p
  have hb : P.natDegree ≤ n :=
    (le_of_eq (MvPolynomial.natDegree_finSuccEquiv p)).trans
      ((MvPolynomial.degreeOf_le_totalDegree p 0).trans hp.totalDegree_le)
  have hP (i : ℕ) : (P.coeff i).IsHomogeneous (n - i) := by
    by_cases hi : i ≤ n
    · exact hp.finSuccEquiv_coeff_isHomogeneous i (n - i) (by omega)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact MvPolynomial.isHomogeneous_zero _ _ _
  have heP : P.eval₂ (MvPolynomial.eval (fun i ↦ f i.succ)) (f 0) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map]
    rw [← MvPolynomial.eval_eq_eval_mv_eval']
    have hf : Fin.cons (f 0) (fun i ↦ f i.succ) = f := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [hf]
    exact he
  have h := a3b1_polynomial_relation_coeff_mem (R := R) (σ := Fin N)
    (fun i : Fin N ↦ f i.succ) hc (f 0) hr
    n n le_rfl P hP hb heP
  intro d
  have hd := h (d 0) d.tail
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hd
  apply (show Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)) ⊔
      Ideal.span {f 0} ≤ Ideal.span (Set.range f) from ?_) hd
  apply sup_le
  · apply Ideal.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨i.succ, rfl⟩
  · apply Ideal.span_le.mpr
    rintro x rfl
    exact Ideal.subset_span ⟨0, rfl⟩

theorem a3b1_reverse_regular_homogeneous_coeff_mem
    {R : Type*} [CommRing R] (N : ℕ) (f : Fin N → R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f).reverse)
    (n : ℕ) (p : MvPolynomial (Fin N) R) (hp : p.IsHomogeneous n)
    (he : p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  induction N generalizing n with
  | zero =>
      have he' : p.eval f = 0 := by simpa using he
      have hp' : p = 0 := by
        apply ((MvPolynomial.aeval_injective_iff_of_isEmpty (R := R)).mpr
          (fun _ _ hxy ↦ hxy))
        simpa [MvPolynomial.aeval_def] using he'
      simp [hp']
  | succ N ih =>
      have hreg' : RingTheory.Sequence.IsWeaklyRegular R
          ((List.ofFn (fun i : Fin N ↦ f i.succ)).reverse ++ [f 0]) := by
        simpa only [List.ofFn_succ, List.reverse_cons] using hreg
      have hprev := (RingTheory.Sequence.isWeaklyRegular_append_iff R _ _).mp hreg' |>.1
      have hc := ih (fun i : Fin N ↦ f i.succ) hprev
      have hr (x : R)
          (hx : f 0 * x ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ))) :
          x ∈ Ideal.span (Set.range (fun i : Fin N ↦ f i.succ)) := by
        rw [a3b1_span_range_eq_ofList_reverse] at hx ⊢
        exact a3b1_regular_append_cancel _ _ hreg' x hx
      obtain ⟨q, hq, hqe, hqc⟩ := a3b1_power_expression_with_ideal_coefficients f n _ he
      have hzero : (p - q).eval f = 0 := by simp [hqe]
      have hz := a3b1_finSucc_zero_eval_coeff_mem f hc hr n (p - q) (hp.sub hq) hzero
      intro d
      have hmem := add_mem (hz d) (hqc d)
      simpa only [MvPolynomial.coeff_sub, sub_add_cancel] using hmem

theorem a3b1_reverse_ofFn_get_rev
    {R : Type*} (rs : List R) :
    (List.ofFn (fun i : Fin rs.length ↦ rs.get i.rev)).reverse = rs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn,
      List.get_eq_getElem, Fin.val_rev]
    congr 1
    omega

end HodgeLean.Adapters
