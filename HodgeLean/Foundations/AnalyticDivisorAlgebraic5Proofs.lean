import HodgeLean.Foundations.AnalyticDivisorAlgebraic4
import HodgeLean.Foundations.AnalyticDivisorAlgebraic5Defs

/-! # Proof obligations for the analytic divisor spec, fifth stage

One obligation per statement of `HodgeLean.Foundations.AnalyticDivisorAlgebraic5`. All eighteen
are open.
-/

noncomputable section

open Set Filter Topology Metric Polynomial

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic5

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4

section Uniqueness

variable {n : ℕ}

theorem spec_weierstrass_preparation_unique_aux {d : ℕ} {u u' : (Fin n → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (Fin n → ℂ) → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hu' : AnalyticAt ℂ u' 0) (ha' : ∀ j, ContinuousAt (a' j) 0) (ha'0 : ∀ j, a' j 0 = 0)
    (h : (fun p => u p * monicInLast a p) =ᶠ[𝓝 0] fun p => u' p * monicInLast a' p) :
    u =ᶠ[𝓝 0] u' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  have hune : ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), u p ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hq : AnalyticAt ℂ (fun p => u' p / u p - 1) 0 :=
    (hu'.div hu hu0).sub analyticAt_const
  obtain ⟨h1, h2⟩ := spec_weierstrass_division_unique ha' ha'0 hq
    (b := fun j z => a' j z - a j z) (by
      filter_upwards [h, hune] with p hp hp0
      have e : ∑ j, (a' j p.1 - a j p.1) * p.2 ^ (j : ℕ) =
          monicInLast a' p - monicInLast a p := by
        simp only [monicInLast, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e]
      field_simp
      linear_combination -hp)
  refine ⟨?_, fun j => (h2 j).mono fun z hz => (sub_eq_zero.1 hz).symm⟩
  filter_upwards [h1, hune] with p hp hp0
  rw [sub_eq_zero, div_eq_one_iff_eq hp0] at hp
  exact hp.symm

theorem spec_not_preparation_unique_of_unit_aux :
    ((fun p : (Fin 1 → ℂ) × ℂ =>
        (1 : ℂ) * monicInLast (fun _ _ => (0 : ℂ) : Fin 1 → (Fin 1 → ℂ) → ℂ) p) =ᶠ[𝓝 0]
      fun p => p.2 / (p.2 - 1) *
        monicInLast (fun _ _ => (-1 : ℂ) : Fin 1 → (Fin 1 → ℂ) → ℂ) p) ∧
    ¬ ((fun _ => (1 : ℂ)) =ᶠ[𝓝 (0 : (Fin 1 → ℂ) × ℂ)] fun p => p.2 / (p.2 - 1)) := by
  refine ⟨?_, fun H => by simpa using H.self_of_nhds⟩
  have : ∀ᶠ p in 𝓝 (0 : (Fin 1 → ℂ) × ℂ), p.2 - 1 ≠ 0 :=
    (continuous_snd.sub continuous_const).continuousAt.eventually_ne (by simp)
  filter_upwards [this] with p hp
  simp only [monicInLast, Fin.sum_univ_one, Fin.val_zero, pow_zero, pow_one, mul_one,
    one_mul]
  field_simp
  ring

end Uniqueness

section Multiplicity

private theorem analyticOrderAt_eq_order_of_hasFPS {g : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hq : HasFPowerSeriesAt g q 0) (hq0 : q ≠ 0) : analyticOrderAt g 0 = q.order := by
  rw [hq.analyticAt.analyticOrderAt_eq_natCast]
  refine ⟨_, (hq.has_fpower_series_iterate_dslope_fslope q.order).analyticAt,
    hq.iterate_dslope_fslope_ne_zero hq0, Eventually.of_forall fun z => ?_⟩
  simpa using hq.eq_pow_order_mul_iterate_dslope z

private theorem analyticOrderAt_of_hasSum_pow_mul {g : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ᶠ t in 𝓝 (0 : ℂ), HasSum (fun k => t ^ k * c k) (g t)) {N : ℕ}
    (hk : ∀ k < N, c k = 0) :
    (N : ℕ∞) ≤ analyticOrderAt g 0 ∧ (c N ≠ 0 → analyticOrderAt g 0 = N) := by
  classical
  set q := FormalMultilinearSeries.ofScalars ℂ c
  have hq : HasFPowerSeriesAt g q 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hs] with t ht
    simpa [q, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using ht
  have hqc : ∀ k, q k = 0 ↔ c k = 0 := fun k => by
    rw [← FormalMultilinearSeries.coeff_eq_zero, FormalMultilinearSeries.coeff_ofScalars]
  by_cases hc : ∃ k, c k ≠ 0
  · have hq0 : ∃ k, q k ≠ 0 := let ⟨k, hk⟩ := hc; ⟨k, fun h => hk ((hqc k).1 h)⟩
    have hq0' : q ≠ 0 := fun h => by obtain ⟨k, hk⟩ := hq0; exact hk (by simp [h])
    rw [analyticOrderAt_eq_order_of_hasFPS hq hq0', FormalMultilinearSeries.order_eq_find hq0]
    refine ⟨?_, fun hN => ?_⟩
    · exact_mod_cast (Nat.le_find_iff _ _).2 fun k hkN => by simpa using (hqc k).2 (hk k hkN)
    · congr 1
      exact (Nat.find_eq_iff _).2 ⟨fun h => hN ((hqc N).1 h),
        fun k hkN => by simpa using (hqc k).2 (hk k hkN)⟩
  · push Not at hc
    have : analyticOrderAt g 0 = ⊤ := by
      rw [analyticOrderAt_eq_top]
      filter_upwards [hs] with t ht
      exact ht.unique (by simp [hc])
    simp [this, hc]

theorem spec_exists_multiplicity_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (hf0 : ¬ ∀ᶠ y in 𝓝 x, f y = 0) :
    ∃ m : ℕ, (∀ v : E, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x + t • v)) 0) ∧
      IsOpen {v : E | analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = m} ∧
      Dense {v : E | analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = m} := by
  classical
  obtain ⟨p, hp⟩ := hf
  set P : ℕ → E → ℂ := fun k y => p k fun _ => y with hPdef
  have hline : ∀ v : E, ∀ᶠ t in 𝓝 (0 : ℂ),
      HasSum (fun k => t ^ k * P k v) (f (x + t • v)) := by
    intro v
    have ht : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    filter_upwards [ht.eventually hp.eventually_hasSum] with t h
    convert h using 2 with k
    rw [hPdef]
    simp only
    rw [show (fun _ : Fin k => t • v) = fun i => (fun _ => t) i • (fun _ => v) i from rfl,
      ContinuousMultilinearMap.map_smul_univ]
    simp [smul_eq_mul]
  have hex : ∃ k, ∃ y, P k y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    filter_upwards [hp.eventually_hasSum_sub] with y hy
    have h0 : ∀ k, (p k fun _ => y - x) = 0 := fun k => hcon k (y - x)
    simp only [h0] at hy
    exact hy.unique hasSum_zero
  set m := Nat.find hex
  have hlt : ∀ k < m, ∀ y, P k y = 0 := fun k hk y => by
    by_contra h
    exact Nat.find_min hex hk ⟨y, h⟩
  have hset : {v : E | analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = m} =
      {v | P m v ≠ 0} := by
    ext v
    simp only [mem_ofPred_eq]
    refine ⟨fun h hm => ?_, fun h =>
      (analyticOrderAt_of_hasSum_pow_mul (hline v) fun k hk => hlt k hk v).2 h⟩
    have := (analyticOrderAt_of_hasSum_pow_mul (N := m + 1) (hline v) fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hlt k hk v
      · exact hm).1
    rw [h] at this
    exact absurd (by exact_mod_cast this : m + 1 ≤ m) (by omega)
  have hPc : Continuous (P m) :=
    (p m).cont.comp (continuous_pi fun _ => continuous_id)
  have hPan : AnalyticOnNhd ℂ (P m) univ := fun y _ =>
    (p m).analyticAt.comp
      ((ContinuousLinearMap.pi fun _ : Fin m => ContinuousLinearMap.id ℂ E).analyticAt y)
  refine ⟨m, fun v => (analyticOrderAt_of_hasSum_pow_mul (hline v) fun k hk => hlt k hk v).1,
    ?_, ?_⟩
  · rw [hset]
    exact isOpen_ne_fun hPc continuous_const
  · rw [hset, dense_iff_inter_open]
    rintro U hU ⟨u, hu⟩
    by_contra hne
    have hz : P m =ᶠ[𝓝 u] 0 := by
      filter_upwards [hU.mem_nhds hu] with y hy
      by_contra h
      exact hne ⟨y, hy, h⟩
    obtain ⟨y, hy⟩ := Nat.find_spec hex
    exact hy (hPan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ u) hz (mem_univ y))

variable {n : ℕ}

theorem spec_not_exists_dense_order_zero_aux :
    ¬ ∃ m : ℕ, Dense {v : (Fin n → ℂ) × ℂ |
      analyticOrderAt (fun t : ℂ => (fun _ : (Fin n → ℂ) × ℂ => (0 : ℂ)) (0 + t • v)) 0 = m} := by
  rintro ⟨m, hm⟩
  obtain ⟨v, hv⟩ := hm.nonempty
  have h0 : analyticOrderAt (fun _ : ℂ => (0 : ℂ)) 0 = ⊤ :=
    analyticOrderAt_eq_top.2 (Eventually.of_forall fun _ => rfl)
  exact ENat.top_ne_natCast m (h0.symm.trans hv)

theorem spec_exists_linearEquiv_preparation_aux {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : ¬ ∀ᶠ p in 𝓝 0, f p = 0) :
    ∃ m : ℕ, (∀ v, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (t • v)) 0) ∧
      ∃ L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ),
        ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
          ∃ a : Fin m → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
            (fun p => f (L p)) =ᶠ[𝓝 0] fun p => u p * monicInLast a p := by
  obtain ⟨m, hle, -, hd⟩ := spec_exists_multiplicity_aux hf hf0
  simp only [zero_add] at hle hd
  refine ⟨m, hle, ?_⟩
  obtain ⟨v, hv0, hv⟩ := hd.inter_open_nonempty {v | v ≠ 0} isOpen_ne
    ⟨((0 : Fin n → ℂ), (1 : ℂ)), by simp⟩
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℂ)
    (show ((0 : Fin n → ℂ), (1 : ℂ)) ≠ 0 by simp) hv0
  have hfL : AnalyticAt ℂ (fun p => f (L p)) 0 := by
    have hL0 : AnalyticAt ℂ (fun p => L p) 0 :=
      (L : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ)).analyticAt 0
    exact hf.comp_of_eq hL0 (map_zero L)
  have hline : (fun w : ℂ => f (L (0, w))) = fun t => f (t • v) := by
    funext w
    rw [← hL, ← map_smul]
    simp
  have hord : analyticOrderAt (fun w => (fun p => f (L p)) (0, w)) 0 = m := by
    rw [hline]
    exact hv
  exact ⟨L, spec_weierstrass_preparation hfL hord⟩

end Multiplicity

section Discriminant

variable {n : ℕ}

theorem gaga5b_degree_sum_lt_monicPoly {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (∑ j : Fin d, C (a j z) * X ^ (j : ℕ)).degree < (X ^ d : ℂ[X]).degree := by
  rw [degree_X_pow]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.2)

theorem spec_monicPoly_aux {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (monicPoly a z).Monic ∧ (monicPoly a z).natDegree = d ∧
      ∀ w, (monicPoly a z).eval w = monicInLast a (z, w) := by
  have hlt := gaga5b_degree_sum_lt_monicPoly a z
  refine ⟨(monic_X_pow d).add_of_left hlt, ?_, fun w => ?_⟩
  · rw [monicPoly, natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]
  · simp [monicPoly, monicInLast, eval_finsetSum]

theorem gaga5b_analyticAt_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
    {M : E → Matrix (Fin m) (Fin m) ℂ} {x : E} (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) x) :
    AnalyticAt ℂ (fun z => (M z).det) x := by
  simp only [Matrix.det_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hM _ _)

/-- Mathlib's `Polynomial.sylvesterDeriv` with the degree replaced by a free natural number `k`,
so that its size does not depend on the polynomial.

Source: Mathlib's `Polynomial.sylvesterDeriv` (`RingTheory/Polynomial/Resultant/Basic.lean`). -/
def gaga5b_sylvesterDerivAt (f : ℂ[X]) (k : ℕ) : Matrix (Fin (k - 1 + k)) (Fin (k - 1 + k)) ℂ :=
  if hk : k = 0 then 0
  else (f.derivative.sylvester f (k - 1) k).updateRow ⟨2 * k - 2, by lia⟩
    (fun j ↦ if ↑j = k - 2 then 1 else (if ↑j = 2 * k - 2 then (k : ℂ) else 0))

example (f : ℂ[X]) : gaga5b_sylvesterDerivAt f 0 = 0 := rfl

theorem gaga5b_discr_eq_sylvesterDerivAt {f : ℂ[X]} {k : ℕ} (hk : f.natDegree = k) :
    f.discr = (gaga5b_sylvesterDerivAt f k).det * (-1) ^ (k * (k - 1) / 2) := by
  subst hk; rfl

theorem gaga5b_coeff_monicPoly {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : ℕ) :
    (monicPoly a z).coeff k =
      (if k = d then 1 else 0) + ∑ j : Fin d, if k = j then a j z else 0 := by
  simp [monicPoly, coeff_X_pow]

theorem gaga5b_analyticAt_coeff_monicPoly {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₀) (k : ℕ) :
    AnalyticAt ℂ (fun z => (monicPoly a z).coeff k) z₀ := by
  simp only [gaga5b_coeff_monicPoly]
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
  split_ifs
  · exact ha j
  · exact analyticAt_const

theorem spec_analyticAt_weierstrassDiscr_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₀ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₀) :
    AnalyticAt ℂ (weierstrassDiscr a) z₀ := by
  have hc := gaga5b_analyticAt_coeff_monicPoly ha
  have hc' : ∀ k, AnalyticAt ℂ (fun z => (derivative (monicPoly a z)).coeff k) z₀ := fun k => by
    simp only [coeff_derivative]
    exact (hc _).mul analyticAt_const
  have : weierstrassDiscr a =
      fun z => (gaga5b_sylvesterDerivAt (monicPoly a z) d).det * (-1) ^ (d * (d - 1) / 2) := by
    funext z; exact gaga5b_discr_eq_sylvesterDerivAt (spec_monicPoly_aux a z).2.1
  rw [this]
  refine AnalyticAt.mul (gaga5b_analyticAt_det fun i j => ?_) analyticAt_const
  unfold gaga5b_sylvesterDerivAt
  split_ifs with hd
  · exact analyticAt_const
  simp only [Matrix.updateRow_apply]
  split_ifs
  all_goals try exact analyticAt_const
  unfold sylvester
  simp only [Matrix.of_apply]
  induction j using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left]
    split_ifs
    · exact hc _
    · exact analyticAt_const
  | right j =>
    simp only [Fin.addCases_right]
    split_ifs
    · exact hc' _
    · exact analyticAt_const

theorem gaga5b_discr_ne_zero_iff_separable {f : ℂ[X]} (hf : f.Monic) : f.discr ≠ 0 ↔ f.Separable := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · have : f = C 1 := by
      rw [eq_C_of_natDegree_eq_zero h0, ← hf.leadingCoeff, leadingCoeff, h0]
    subst this
    rw [discr_C]; simp
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.1 hpos
  have hres := resultant_deriv hdeg
  rw [← natDegree_derivative] at hres
  rw [hf.leadingCoeff, mul_one] at hres
  have hiff : f.discr = 0 ↔ resultant f (derivative f) = 0 := by
    rw [hres]; simp
  rw [Ne, hiff, resultant_eq_zero_iff]
  simp [hf.ne_zero, Separable]

theorem spec_weierstrassDiscr_ne_zero_iff_aux {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    weierstrassDiscr a z ≠ 0 ↔ ∀ w, analyticOrderAt (fun w => monicInLast a (z, w)) w ≤ 1 := by
  classical
  obtain ⟨hm, -, heval⟩ := spec_monicPoly_aux a z
  have hfun : (fun w => monicInLast a (z, w)) = fun w => (monicPoly a z).eval w := by
    funext w; exact (heval w).symm
  rw [hfun, weierstrassDiscr, gaga5b_discr_ne_zero_iff_separable hm,
    ← nodup_roots_iff_of_splits hm.ne_zero (IsAlgClosed.splits _), Multiset.nodup_iff_count_le_one]
  refine forall_congr' fun w => ?_
  rw [spec_analyticOrderAt_polynomial_eval hm.ne_zero, count_roots]
  exact_mod_cast Iff.rfl

theorem gaga5b_monicInLast_slice_eq {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (fun w => monicInLast a (z, w)) = fun w => (monicPoly a z).eval w := by
  funext w; exact ((spec_monicPoly_aux a z).2.2 w).symm

theorem gaga5b_analyticOrderAt_monicInLast_slice {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) :
    analyticOrderAt (fun w => monicInLast a (z, w)) w = (monicPoly a z).rootMultiplicity w := by
  rw [gaga5b_monicInLast_slice_eq, spec_analyticOrderAt_polynomial_eval (spec_monicPoly_aux a z).1.ne_zero]

theorem gaga5b_analyticOrderNatAt_monicInLast_slice {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) :
    analyticOrderNatAt (fun w => monicInLast a (z, w)) w = (monicPoly a z).rootMultiplicity w := by
  rw [analyticOrderNatAt, gaga5b_analyticOrderAt_monicInLast_slice, ENat.toNat_natCast]

/-- The zero count of a slice of `monicInLast` in a disc is the number of roots of `monicPoly`
in the disc, with multiplicity. -/
theorem gaga5b_zeroCount_monicInLast_slice {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (c : ℂ) (r : ℝ) [DecidablePred (· ∈ ball c r)] :
    zeroCount (fun w => monicInLast a (z, w)) c r =
      ∑ β ∈ (monicPoly a z).roots.toFinset.filter (· ∈ ball c r),
        (monicPoly a z).rootMultiplicity β := by
  have hne := (spec_monicPoly_aux a z).1.ne_zero
  rw [zeroCount]
  simp_rw [gaga5b_analyticOrderNatAt_monicInLast_slice]
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_
  · rintro β ⟨hβ, hs⟩
    simp only [Function.mem_support, ne_eq, rootMultiplicity_eq_zero_iff, not_imp] at hs
    rw [Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne]
    exact ⟨hs.1, hβ⟩
  · intro β hβ
    simp only [Finset.coe_filter, mem_ofPred_eq] at hβ
    exact hβ.2

theorem gaga5b_weightedSum_monicInLast_slice {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (c : ℂ) (r : ℝ) [DecidablePred (· ∈ ball c r)] :
    ∑ᶠ (β : ℂ) (_ : β ∈ ball c r),
        (analyticOrderNatAt (fun w => monicInLast a (z, w)) β : ℂ) * β =
      ∑ β ∈ (monicPoly a z).roots.toFinset.filter (· ∈ ball c r),
        ((monicPoly a z).rootMultiplicity β : ℂ) * β := by
  have hne := (spec_monicPoly_aux a z).1.ne_zero
  simp_rw [gaga5b_analyticOrderNatAt_monicInLast_slice]
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_
  · rintro β ⟨hβ, hs⟩
    simp only [Function.mem_support, ne_eq, mul_eq_zero, Nat.cast_eq_zero,
      rootMultiplicity_eq_zero_iff, not_or, not_imp] at hs
    rw [Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne]
    exact ⟨hs.1.1, hβ⟩
  · intro β hβ
    simp only [Finset.coe_filter, mem_ofPred_eq] at hβ
    exact hβ.2

theorem gaga5b_analyticAt_monicInLast {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z) (ζ : ℂ) : AnalyticAt ℂ (monicInLast a) (z, ζ) := by
  show AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ))
    (z, ζ)
  exact (analyticAt_snd.pow d).add (Finset.analyticAt_fun_sum _ fun j _ =>
    ((ha j).comp analyticAt_fst).mul (analyticAt_snd.pow _))

/-- Discs of pairwise disjoint radii around the roots of `monicPoly a z₁`, on whose boundary
circles `monicInLast a (z, ·)` does not vanish for `z` near `z₁`, each containing as many zeros as
the multiplicity of its centre. -/
theorem gaga5b_exists_root_discs {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₁ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₁) :
    ∃ r : ℂ → ℝ, (∀ α ∈ (monicPoly a z₁).roots.toFinset, 0 < r α) ∧
      (∀ α ∈ (monicPoly a z₁).roots.toFinset, ∀ β ∈ (monicPoly a z₁).roots.toFinset, ∀ w,
        w ∈ ball α (r α) → w ∈ ball β (r β) → α = β) ∧
      ∀ᶠ z in 𝓝 z₁, ∀ α ∈ (monicPoly a z₁).roots.toFinset,
        (∀ w ∈ sphere α (r α), monicInLast a (z, w) ≠ 0) ∧
        zeroCount (fun w => monicInLast a (z, w)) α (r α) =
          (monicPoly a z₁).rootMultiplicity α := by
  set S := (monicPoly a z₁).roots.toFinset
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ p ∈ S ×ˢ S, p.1 ≠ p.2 → 2 * ε < ‖p.1 - p.2‖ := by
    refine (eventually_mem_nhdsWithin).and ((eventually_all_finset _).2 fun p _ => ?_)
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    have h0 : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), 2 * ε < ‖p.1 - p.2‖ :=
      (continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const
        (by simpa using h0)
    exact Eventually.filter_mono nhdsWithin_le_nhds (this.mono fun _ h _ => h)
  obtain ⟨ε, hε0, hεS⟩ := hε.exists
  have H : ∀ α ∈ S, ∃ r, 0 < r ∧ r < ε ∧ ∃ δ, 0 < δ ∧
      (∀ z ∈ closedBall z₁ δ, ∀ w ∈ sphere α r, monicInLast a (z, w) ≠ 0) ∧
      ∀ z ∈ ball z₁ δ, zeroCount (fun w => monicInLast a (z, w)) α r =
        (monicPoly a z₁).rootMultiplicity α := fun α _ => by
    obtain ⟨r, hr, hrε, δ, hδ, -, hne, hc⟩ := spec_exists_zeroCount_eq_order
      (gaga5b_analyticAt_monicInLast ha α) (gaga5b_analyticOrderAt_monicInLast_slice a z₁ α) hε0
    exact ⟨r, hr, hrε, δ, hδ, hne, hc⟩
  choose! r hr hrε δ hδ hne hc using H
  refine ⟨r, hr, fun α hα β hβ w hwα hwβ => ?_, ?_⟩
  · by_contra hab
    have h1 := hεS (α, β) (Finset.mem_product.2 ⟨hα, hβ⟩) hab
    have h2 : ‖α - β‖ < 2 * ε := by
      calc ‖α - β‖ ≤ dist w α + dist w β := by
              rw [← dist_eq_norm]; exact dist_triangle_left α β w
        _ < r α + r β := add_lt_add hwα hwβ
        _ < ε + ε := add_lt_add (hrε α hα) (hrε β hβ)
        _ = 2 * ε := by ring
    exact lt_irrefl _ (h1.trans h2)
  · refine (eventually_all_finset _).2 fun α hα => ?_
    filter_upwards [ball_mem_nhds z₁ (hδ α hα)] with z hz
    exact ⟨hne α hα z (ball_subset_closedBall hz), hc α hα z hz⟩

theorem gaga5b_exists_root_mem_ball_of_zeroCount_pos {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} {c : ℂ} {r : ℝ}
    (h : 0 < zeroCount (fun w => monicInLast a (z, w)) c r) :
    ∃ β ∈ (monicPoly a z).roots.toFinset, β ∈ ball c r := by
  classical
  rw [gaga5b_zeroCount_monicInLast_slice] at h
  obtain ⟨β, hβ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  simp only [Finset.mem_filter] at hβ
  exact ⟨β, hβ⟩

theorem spec_eventually_card_roots_le_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₁ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₁) :
    ∀ᶠ z in 𝓝 z₁,
      (monicPoly a z₁).roots.toFinset.card ≤ (monicPoly a z).roots.toFinset.card := by
  obtain ⟨r, hr, hdisj, hev⟩ := gaga5b_exists_root_discs ha
  filter_upwards [hev] with z hz
  have H : ∀ α ∈ (monicPoly a z₁).roots.toFinset,
      ∃ β ∈ (monicPoly a z).roots.toFinset, β ∈ ball α (r α) := fun α hα => by
    refine gaga5b_exists_root_mem_ball_of_zeroCount_pos ?_
    rw [(hz α hα).2]
    have hne := (spec_monicPoly_aux a z₁).1.ne_zero
    exact (rootMultiplicity_pos hne).2 (by simpa [hne] using hα)
  choose! β hβ hβr using H
  exact Finset.card_le_card_of_injOn β (fun α hα => hβ α hα)
    (fun α hα α' hα' h => hdisj α hα α' hα' (β α) (hβr α hα) (h ▸ hβr α' hα'))

theorem gaga5b_analyticAt_eval_family {Q : (Fin n → ℂ) → ℂ[X]} {N : ℕ} {z₀ : Fin n → ℂ}
    (hN : ∀ z, (Q z).natDegree < N) (hQ : ∀ k, AnalyticAt ℂ (fun z => (Q z).coeff k) z₀)
    (w : ℂ) : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => (Q p.1).eval p.2) (z₀, w) := by
  have : (fun p : (Fin n → ℂ) × ℂ => (Q p.1).eval p.2) =
      fun p => ∑ i ∈ Finset.range N, (Q p.1).coeff i * p.2 ^ i := by
    funext p; exact eval_eq_sum_range' (hN p.1) p.2
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  have h1 := (hQ i).comp (analyticAt_fst (p := (z₀, w)))
  exact h1.mul (analyticAt_snd.pow i)

theorem gaga5b_deriv_monicInLast_slice {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (w : ℂ) :
    deriv (fun w => monicInLast a (z, w)) w = (derivative (monicPoly a z)).eval w := by
  rw [gaga5b_monicInLast_slice_eq, Polynomial.deriv]

theorem spec_exists_root_graphs_pow_aux {d k : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₁ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₁)
    (hk : ∀ᶠ z in 𝓝 z₁, (monicPoly a z).roots.toFinset.card = k) :
    ∃ φ : Fin k → (Fin n → ℂ) → ℂ, ∃ m : Fin k → ℕ, (∀ i, AnalyticAt ℂ (φ i) z₁ ∧ 1 ≤ m i) ∧
      ∀ᶠ z in 𝓝 z₁, (∀ w, monicInLast a (z, w) = ∏ i, (w - φ i z) ^ m i) ∧
        Pairwise fun i j => φ i z ≠ φ j z := by
  classical
  obtain ⟨r, hr, hdisj, hev⟩ := gaga5b_exists_root_discs ha
  have hne₁ := (spec_monicPoly_aux a z₁).1.ne_zero
  have hcard : (monicPoly a z₁).roots.toFinset.card = k := hk.self_of_nhds
  let e : (monicPoly a z₁).roots.toFinset ≃ Fin k :=
    (monicPoly a z₁).roots.toFinset.equivFinOfCardEq hcard
  let α : Fin k → ℂ := fun i => (e.symm i : ℂ)
  have hα : ∀ i, α i ∈ (monicPoly a z₁).roots.toFinset := fun i => (e.symm i).2
  have hαinj : Function.Injective α := fun i j h => e.symm.injective (Subtype.ext h)
  let m : Fin k → ℕ := fun i => (monicPoly a z₁).rootMultiplicity (α i)
  have hm : ∀ i, 1 ≤ m i := fun i =>
    (rootMultiplicity_pos hne₁).2 (by simpa [hne₁] using hα i)
  let F : (Fin n → ℂ) × ℂ → ℂ := fun p =>
    p.2 * (derivative (monicPoly a p.1)).eval p.2 / (monicPoly a p.1).eval p.2
  let φ : Fin k → (Fin n → ℂ) → ℂ := fun i z =>
    (∮ w in C(α i, r (α i)), F (z, w)) / (2 * Real.pi * Complex.I * m i)
  -- the circle integral computes the root in each disc
  have hφeq : ∀ z i, (∀ w ∈ sphere (α i) (r (α i)), monicInLast a (z, w) ≠ 0) →
      φ i z = (∑ β ∈ (monicPoly a z).roots.toFinset.filter (· ∈ ball (α i) (r (α i))),
        ((monicPoly a z).rootMultiplicity β : ℂ) * β) / (m i : ℂ) := by
    intro z i hs
    have hint : (∮ w in C(α i, r (α i)), F (z, w)) =
        ∮ w in C(α i, r (α i)), id w * deriv (fun w => monicInLast a (z, w)) w /
          monicInLast a (z, w) := by
      congr 1; funext w
      simp only [F, id, gaga5b_deriv_monicInLast_slice, (spec_monicPoly_aux a z).2.2]
    have hg : AnalyticOnNhd ℂ (fun w => monicInLast a (z, w)) (closedBall (α i) (r (α i))) := by
      intro w _; rw [gaga5b_monicInLast_slice_eq]; exact (Polynomial.differentiable _).analyticAt w
    show (∮ w in C(α i, r (α i)), F (z, w)) / _ = _
    rw [hint, spec_circleIntegral_mul_logDeriv (hr _ (hα i)) hg (fun w _ => analyticAt_id) hs]
    simp only [id]
    rw [gaga5b_weightedSum_monicInLast_slice, mul_div_mul_left]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero
  have hdegP : ∀ z, (monicPoly a z).natDegree < d + 1 := fun z => by
    rw [(spec_monicPoly_aux a z).2.1]; omega
  have hdegP' : ∀ z, (derivative (monicPoly a z)).natDegree < d + 1 := fun z =>
    lt_of_le_of_lt (natDegree_derivative_le _) (by rw [(spec_monicPoly_aux a z).2.1]; omega)
  have hcP' : ∀ j, AnalyticAt ℂ (fun z => (derivative (monicPoly a z)).coeff j) z₁ := fun j => by
    simp only [coeff_derivative]
    exact (gaga5b_analyticAt_coeff_monicPoly ha _).mul analyticAt_const
  refine ⟨φ, m, fun i => ⟨?_, hm i⟩, ?_⟩
  · have hF : AnalyticOnNhd ℂ F ({z₁} ×ˢ sphere (α i) (r (α i))) := by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      rw [mem_singleton_iff] at hz
      subst hz
      have hP : (monicPoly a z).eval w ≠ 0 := by
        rw [(spec_monicPoly_aux a z).2.2]; exact (hev.self_of_nhds (α i) (hα i)).1 w hw
      exact (analyticAt_snd.mul (gaga5b_analyticAt_eval_family hdegP' hcP' w)).div
        (gaga5b_analyticAt_eval_family hdegP (gaga5b_analyticAt_coeff_monicPoly ha) w) hP
    exact (spec_analyticOnNhd_circleIntegral (hr _ (hα i)) hF z₁ rfl).div_const
  filter_upwards [hev, hk] with z hz hkz
  have hne := (spec_monicPoly_aux a z).1.ne_zero
  set R := (monicPoly a z).roots.toFinset with hR
  let t : Fin k → Finset ℂ := fun i => R.filter (· ∈ ball (α i) (r (α i)))
  have hsum : ∀ i, ∑ β ∈ t i, (monicPoly a z).rootMultiplicity β = m i := fun i => by
    rw [← gaga5b_zeroCount_monicInLast_slice]; exact (hz (α i) (hα i)).2
  have htne : ∀ i, 1 ≤ (t i).card := fun i => by
    refine Finset.card_pos.2 (Finset.nonempty_of_sum_ne_zero (f := fun β =>
      (monicPoly a z).rootMultiplicity β) ?_)
    rw [hsum]; have := hm i; omega
  have htdisj : ∀ i j, i ≠ j → Disjoint (t i) (t j) := fun i j hij => by
    refine Finset.disjoint_left.2 fun β hi hj => hij (hαinj ?_)
    exact hdisj _ (hα i) _ (hα j) β (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2
  have hsub : Finset.univ.biUnion t ⊆ R := Finset.biUnion_subset.2 fun i _ => Finset.filter_subset _ _
  have hcardU : (Finset.univ.biUnion t).card = ∑ i, (t i).card :=
    Finset.card_biUnion fun i _ j _ hij => htdisj i j hij
  have hle : ∑ i, (t i).card ≤ k := by
    rw [← hcardU]; exact (Finset.card_le_card hsub).trans hkz.le
  have h1 : ∀ i, (t i).card = 1 := by
    by_contra! H
    obtain ⟨j, hj⟩ := H
    have : ∑ _i : Fin k, 1 < ∑ i, (t i).card :=
      Finset.sum_lt_sum (fun i _ => htne i) ⟨j, Finset.mem_univ _, by have := htne j; omega⟩
    simp at this
    omega
  have hU : Finset.univ.biUnion t = R := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcardU, hkz, Finset.sum_congr rfl fun i _ => h1 i]; simp
  choose β hβ using fun i => Finset.card_eq_one.1 (h1 i)
  have hβmem : ∀ i, β i ∈ ball (α i) (r (α i)) := fun i =>
    (Finset.mem_filter.1 (show β i ∈ t i by rw [hβ i]; exact Finset.mem_singleton_self _)).2
  have hβinj : Function.Injective β := fun i j h =>
    hαinj (hdisj _ (hα i) _ (hα j) (β i) (hβmem i) (h ▸ hβmem j))
  have hmult : ∀ i, (monicPoly a z).rootMultiplicity (β i) = m i := fun i => by
    rw [← hsum i, hβ i, Finset.sum_singleton]
  have hφβ : ∀ i, φ i z = β i := fun i => by
    rw [hφeq z i (hz (α i) (hα i)).1]
    change (∑ x ∈ t i, _) / _ = _
    rw [hβ i, Finset.sum_singleton, hmult i, mul_div_cancel_left₀]
    have := hm i
    exact_mod_cast (by omega : m i ≠ 0)
  have hRim : R = Finset.univ.image β := by
    rw [← hU]; ext x; simp [hβ, eq_comm]
  refine ⟨fun w => ?_, fun i j hij => by
    show φ i z ≠ φ j z
    rw [hφβ, hφβ]; exact hβinj.ne hij⟩
  rw [← (spec_monicPoly_aux a z).2.2,
    (IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (spec_monicPoly_aux a z).1,
    Finset.prod_multiset_map_count, ← hR, hRim, Finset.prod_image fun i _ j _ h => hβinj h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [count_roots, hmult, hφβ]

theorem gaga5b_card_roots_toFinset_le {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (monicPoly a z).roots.toFinset.card ≤ d := by
  refine (Multiset.toFinset_card_le _).trans ?_
  rw [IsAlgClosed.card_roots_eq_natDegree, (spec_monicPoly_aux a z).2.1]

theorem spec_exists_root_graphs_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₀) (hD : weierstrassDiscr a z₀ ≠ 0) :
    ∃ φ : Fin d → (Fin n → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (φ i) z₀) ∧
      ∀ᶠ z in 𝓝 z₀, (∀ w, monicInLast a (z, w) = ∏ i, (w - φ i z)) ∧
        Pairwise fun i j => φ i z ≠ φ j z := by
  classical
  have hmul : ∀ w, (monicPoly a z₀).rootMultiplicity w ≤ 1 := fun w => by
    have := (spec_weierstrassDiscr_ne_zero_iff_aux a z₀).1 hD w
    rw [gaga5b_analyticOrderAt_monicInLast_slice] at this
    exact_mod_cast this
  have hnodup : (monicPoly a z₀).roots.Nodup :=
    Multiset.nodup_iff_count_le_one.2 fun w => by rw [count_roots]; exact hmul w
  have hcard₀ : (monicPoly a z₀).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree,
      (spec_monicPoly_aux a z₀).2.1]
  have hk : ∀ᶠ z in 𝓝 z₀, (monicPoly a z).roots.toFinset.card = d := by
    filter_upwards [spec_eventually_card_roots_le_aux ha] with z hz
    exact le_antisymm (gaga5b_card_roots_toFinset_le a z) (hcard₀.symm.le.trans hz)
  obtain ⟨φ, m, hφ, hev⟩ := spec_exists_root_graphs_pow_aux ha hk
  have hm1 : ∀ i, m i = 1 := by
    have hpoly : monicPoly a z₀ = ∏ i, (X - C (φ i z₀)) ^ m i := by
      refine Polynomial.funext fun w => ?_
      rw [(spec_monicPoly_aux a z₀).2.2, hev.self_of_nhds.1 w, eval_prod]
      simp
    have hdeg : ∑ i, m i = d := by
      have := congrArg natDegree hpoly
      rw [(spec_monicPoly_aux a z₀).2.1, natDegree_prod _ _ fun i _ =>
        pow_ne_zero _ (X_sub_C_ne_zero _)] at this
      simp only [natDegree_pow, natDegree_X_sub_C, mul_one] at this
      exact this.symm
    by_contra! H
    obtain ⟨j, hj⟩ := H
    have : ∑ _i : Fin d, 1 < ∑ i, m i :=
      Finset.sum_lt_sum (fun i _ => (hφ i).2) ⟨j, Finset.mem_univ _, by have := (hφ j).2; omega⟩
    simp at this
    omega
  refine ⟨φ, fun i => (hφ i).1, hev.mono fun z hz => ⟨fun w => ?_, hz.2⟩⟩
  rw [hz.1 w]
  simp [hm1]

theorem gaga5b_not_exists_sq_eq_id {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), ψ t ^ 2 = t) : False := by
  have h1 : analyticOrderAt (ψ ^ 2) 0 = analyticOrderAt (id : ℂ → ℂ) 0 :=
    analyticOrderAt_congr (h.mono fun t ht => by simpa using ht)
  rw [analyticOrderAt_pow hψ, analyticOrderAt_id] at h1
  rcases ENat.ne_top_iff_exists.1 (show analyticOrderAt ψ 0 ≠ ⊤ by
    intro h2; rw [h2] at h1; simp at h1) with ⟨k, hk⟩
  rw [← hk] at h1
  rw [nsmul_eq_mul] at h1
  have : 2 * k = 1 := by exact_mod_cast h1
  omega

theorem spec_not_exists_root_graphs_sq_sub_aux :
    weierstrassDiscr (![fun z => -z 0, fun _ => 0] : Fin 2 → (Fin 1 → ℂ) → ℂ) 0 = 0 ∧
    ¬ ∃ φ : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (φ i) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ w,
        monicInLast (![fun z => -z 0, fun _ => 0] : Fin 2 → (Fin 1 → ℂ) → ℂ) (z, w) =
          ∏ i, (w - φ i z) := by
  set a : Fin 2 → (Fin 1 → ℂ) → ℂ := ![fun z => -z 0, fun _ => 0]
  refine ⟨?_, ?_⟩
  · obtain ⟨hm, hd, -⟩ := spec_monicPoly_aux a 0
    have hdeg : (monicPoly a 0).degree = 2 := by
      rw [degree_eq_natDegree hm.ne_zero, hd]; rfl
    rw [weierstrassDiscr, discr_of_degree_eq_two hdeg, gaga5b_coeff_monicPoly, gaga5b_coeff_monicPoly]
    simp [a, Fin.sum_univ_two]
  · rintro ⟨φ, hφ, hev⟩
    have hsq : ∀ᶠ z in 𝓝 (0 : Fin 1 → ℂ), φ 0 z ^ 2 = z 0 := hev.mono fun z hz => by
      have := hz (φ 0 z)
      simp [monicInLast, a, Fin.sum_univ_two, Fin.prod_univ_two] at this
      linear_combination this
    have hL : AnalyticAt ℂ (fun t : ℂ => (fun _ : Fin 1 => t)) 0 :=
      analyticAt_pi_iff.2 fun _ => analyticAt_id
    have hT : Tendsto (fun t : ℂ => (fun _ : Fin 1 => t)) (𝓝 0) (𝓝 0) := by
      exact hL.continuousAt.tendsto
    refine gaga5b_not_exists_sq_eq_id (ψ := fun t => φ 0 fun _ => t) ?_ ?_
    · exact (hφ 0).comp_of_eq hL rfl
    · exact (hT.eventually hsq).mono fun t ht => ht

end Discriminant

section Reduced

variable {n : ℕ}

/-- `monicInLast a` is analytic at `(z, ζ)` when every coefficient is analytic at `z`. -/
theorem laneC_analyticAt_monicInLast {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z) (ζ : ℂ) : AnalyticAt ℂ (monicInLast a) (z, ζ) := by
  show AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ))
    (z, ζ)
  exact (analyticAt_snd.pow d).add (Finset.analyticAt_fun_sum _ fun j _ =>
    ((ha j).comp analyticAt_fst).mul (analyticAt_snd.pow _))

/-- A zero of order one has nonzero derivative. -/
theorem laneC_deriv_ne_zero_of_order_one {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x)
    (h1 : analyticOrderAt g x = 1) : deriv g x ≠ 0 := by
  have hx : g x = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [h1]; exact one_ne_zero)
  have h := hg.analyticOrderAt_deriv_add_one
  simp only [hx, sub_zero, h1] at h
  have h0 : analyticOrderAt (deriv g) x = 0 := by
    generalize analyticOrderAt (deriv g) x = k at h
    induction k using ENat.recTopCoe with
    | top => simp at h
    | coe k => norm_cast at h ⊢; omega
  exact (analyticOrderAt_eq_zero.mp h0).resolve_left (not_not.mpr hg.deriv)

/-- The order of `w ↦ monicInLast a (z, w)` at any point is a natural number. -/
theorem laneC_order_monicInLast_natCast {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (w : ℂ) : ∃ m : ℕ, analyticOrderAt (fun w => monicInLast a (z, w)) w = m := by
  obtain ⟨hmon, -, hev⟩ := spec_monicPoly_aux a z
  have hfun : (fun w => monicInLast a (z, w)) = fun w => (monicPoly a z).eval w := by
    funext w; rw [hev]
  rw [hfun, spec_analyticOrderAt_polynomial_eval hmon.ne_zero]
  exact ⟨_, rfl⟩

/-- The order of `w ↦ ∏ j, (w - φ j) ^ m j` at `φ i` is `m i` when the `φ j` are distinct. -/
theorem laneC_analyticOrderAt_prod_pow {k : ℕ} {φ : Fin k → ℂ} (m : Fin k → ℕ)
    (hφ : Pairwise fun i j => φ i ≠ φ j) (i : Fin k) :
    analyticOrderAt (fun w => ∏ j, (w - φ j) ^ m j) (φ i) = m i := by
  have hfun : (fun w => ∏ j, (w - φ j) ^ m j) =
      ((· - φ i) ^ m i) * fun w => ∏ j ∈ Finset.univ.erase i, (w - φ j) ^ m j := by
    funext w
    simp only [Pi.mul_apply, Pi.pow_apply]
    exact (Finset.mul_prod_erase _ (fun j => (w - φ j) ^ m j) (Finset.mem_univ i)).symm
  have h2 : AnalyticAt ℂ (fun w => ∏ j ∈ Finset.univ.erase i, (w - φ j) ^ m j) (φ i) :=
    Finset.analyticAt_fun_prod _ fun j _ => (analyticAt_id.sub analyticAt_const).pow _
  have h20 : analyticOrderAt (fun w => ∏ j ∈ Finset.univ.erase i, (w - φ j) ^ m j) (φ i) = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact pow_ne_zero _ (sub_ne_zero.mpr (hφ (Finset.ne_of_mem_erase hj).symm))
  rw [hfun, analyticOrderAt_mul (by fun_prop) h2, h20, analyticOrderAt_centeredMonomial, add_zero]

theorem spec_weierstrassDiscr_not_eventually_zero_aux {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) (ha0 : ∀ j, a j 0 = 0)
    (hsq : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y) :
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 := by
  classical
  intro hD0
  obtain ⟨ε₀, hε₀, hsq₀⟩ := Metric.eventually_nhds_iff_ball.mp hsq
  have hsmall := spec_monicInLast_roots_small (fun j => (ha j).continuousAt) ha0 hε₀
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j => (ha j).eventually_analyticAt
  have hz0 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ ball (0 : Fin n → ℂ) ε₀ := ball_mem_nhds 0 hε₀
  obtain ⟨η, hη, hηP⟩ :=
    Metric.eventually_nhds_iff_ball.mp (((hD0.and hsmall).and hall).and hz0)
  -- the number of distinct roots
  set c : (Fin n → ℂ) → ℕ := fun z => (monicPoly a z).roots.toFinset.card with hc
  have hcd : ∀ z, c z ≤ d := by
    intro z
    obtain ⟨-, hdeg, -⟩ := spec_monicPoly_aux a z
    calc c z ≤ (monicPoly a z).roots.card := Multiset.toFinset_card_le _
      _ ≤ (monicPoly a z).natDegree := card_roots' _
      _ = d := hdeg
  set T : Finset ℕ := (Finset.range (d + 1)).filter fun k => ∃ z ∈ ball (0 : Fin n → ℂ) η, c z = k
  have hT : T.Nonempty :=
    ⟨c 0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hcd 0)),
      0, mem_ball_self hη, rfl⟩⟩
  obtain ⟨-, z₁, hz₁, hz₁k⟩ := Finset.mem_filter.mp (T.max'_mem hT)
  have hmax : ∀ z ∈ ball (0 : Fin n → ℂ) η, c z ≤ c z₁ := by
    intro z hz
    rw [hz₁k]
    exact T.le_max' _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hcd z)), z, hz, rfl⟩)
  obtain ⟨⟨⟨hDz₁, hsmz₁⟩, haz₁⟩, hz₁ε⟩ := hηP z₁ hz₁
  have hk : ∀ᶠ z in 𝓝 z₁, c z = c z₁ := by
    filter_upwards [spec_eventually_card_roots_le_aux haz₁, isOpen_ball.mem_nhds hz₁] with z h1 h2
    exact le_antisymm (hmax z h2) h1
  obtain ⟨φ, m, hφ, hev⟩ := spec_exists_root_graphs_pow_aux haz₁ hk
  obtain ⟨hprod₁, hdist₁⟩ := hev.self_of_nhds
  -- a root of order at least two at `z₁`
  have hnot : ¬ ∀ w, analyticOrderAt (fun w => monicInLast a (z₁, w)) w ≤ 1 :=
    fun h => (spec_weierstrassDiscr_ne_zero_iff_aux a z₁).mpr h hDz₁
  push Not at hnot
  obtain ⟨w₀, hw₀⟩ := hnot
  have hfun : (fun w => monicInLast a (z₁, w)) = fun w => ∏ i, (w - φ i z₁) ^ m i :=
    funext hprod₁
  have hw₀0 : monicInLast a (z₁, w₀) = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun w => monicInLast a (z₁, w))
      (ne_of_gt (lt_of_le_of_lt bot_le hw₀))
  rw [hprod₁, Finset.prod_eq_zero_iff] at hw₀0
  obtain ⟨i, -, hi⟩ := hw₀0
  have hwi : w₀ = φ i z₁ := sub_eq_zero.mp (pow_eq_zero_iff'.mp hi).1
  have hmi : 2 ≤ m i := by
    rw [hfun, hwi, laneC_analyticOrderAt_prod_pow (φ := fun j => φ j z₁) m hdist₁ i] at hw₀
    exact_mod_cast hw₀
  -- `P` is not square-free at `(z₁, φ i z₁)`
  have hy : ((z₁, φ i z₁) : (Fin n → ℂ) × ℂ) ∈ ball 0 ε₀ := by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    refine ⟨mem_ball_zero_iff.mp hz₁ε, hsmz₁ _ ?_⟩
    rw [hprod₁, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, by simp [Nat.pos_iff_ne_zero.mp (by omega : 0 < m i)]⟩
  apply hsq₀ _ hy (fun p => p.2 - φ i p.1)
    (fun p => (p.2 - φ i p.1) ^ (m i - 2) *
      ∏ j ∈ Finset.univ.erase i, (p.2 - φ j p.1) ^ m j)
  · exact analyticAt_snd.sub ((hφ i).1.comp analyticAt_fst)
  · exact (analyticAt_snd.sub ((hφ i).1.comp analyticAt_fst)).pow _ |>.mul
      (Finset.analyticAt_fun_prod _ fun j _ =>
        (analyticAt_snd.sub ((hφ j).1.comp analyticAt_fst)).pow _)
  · simp
  · have hev' : ∀ᶠ p in 𝓝 ((z₁, φ i z₁) : (Fin n → ℂ) × ℂ),
        ∀ w, monicInLast a (p.1, w) = ∏ j, (w - φ j p.1) ^ m j :=
      (continuous_fst.tendsto ((z₁, φ i z₁) : (Fin n → ℂ) × ℂ)).eventually
        (p := fun z => ∀ w, monicInLast a (z, w) = ∏ j, (w - φ j z) ^ m j)
        (hev.mono fun z hz => hz.1)
    filter_upwards [hev'] with p hp
    rw [show p = (p.1, p.2) from rfl, hp p.2,
      ← Finset.mul_prod_erase _ (fun j => (p.2 - φ j p.1) ^ m j) (Finset.mem_univ i)]
    rw [← mul_assoc, ← pow_add, show 2 + (m i - 2) = m i by omega]

/-- A function nonzero at `y` is square-free at `y`. -/
theorem laneC_isSquareFreeAt_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} (hy : f y ≠ 0) : IsSquareFreeAt f y := by
  intro g h _ _ hg0 H
  apply hy
  have := H.self_of_nhds
  simp only [hg0] at this
  simpa using this

theorem spec_weierstrassDiscr_sub_one_sq_aux :
    (∀ᶠ y in 𝓝 (0 : (Fin 1 → ℂ) × ℂ),
      IsSquareFreeAt (monicInLast (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ)) y) ∧
    ∀ z, weierstrassDiscr (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ) z = 0 := by
  have hP : ∀ p : (Fin 1 → ℂ) × ℂ,
      monicInLast (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ) p = (p.2 - 1) ^ 2 := by
    intro p
    simp [monicInLast, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun p : (Fin 1 → ℂ) × ℂ => (p.2 - 1) ^ 2) 0 := by fun_prop
    have h0 : ((fun p : (Fin 1 → ℂ) × ℂ => (p.2 - 1) ^ 2) 0) ≠ 0 := by norm_num
    filter_upwards [hc.eventually_ne h0] with y hy
    exact laneC_isSquareFreeAt_of_ne_zero (by rw [hP]; exact hy)
  · intro z
    have hq : monicPoly (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ) z
        = X ^ 2 + C (-2) * X + C 1 := by
      simp [monicPoly, Fin.sum_univ_two]
      ring
    have hdeg : (X ^ 2 + C (-2 : ℂ) * X + C 1).degree = 2 := by compute_degree!
    rw [weierstrassDiscr, hq, discr_of_degree_eq_two hdeg]
    simp [coeff_X, coeff_C, coeff_one]
    norm_num

theorem spec_weierstrassDiscr_sq_aux :
    ¬ IsSquareFreeAt (monicInLast (fun _ _ => 0 : Fin 2 → (Fin 1 → ℂ) → ℂ)) 0 ∧
    ∀ z, weierstrassDiscr (fun _ _ => 0 : Fin 2 → (Fin 1 → ℂ) → ℂ) z = 0 := by
  refine ⟨fun H => H (fun p => p.2) (fun _ => 1) analyticAt_snd analyticAt_const rfl
    (Eventually.of_forall fun p => by simp [monicInLast]), fun z => ?_⟩
  have hq : monicPoly (fun _ _ => 0 : Fin 2 → (Fin 1 → ℂ) → ℂ) z = X ^ 2 := by
    simp [monicPoly]
  have hdeg : (X ^ 2 : ℂ[X]).degree = 2 := by compute_degree!
  rw [weierstrassDiscr, hq, discr_of_degree_eq_two hdeg]
  simp [coeff_X_pow]

end Reduced

section Regular

variable {n : ℕ}

/-- If every coefficient is analytic at `0` and the discriminant is not locally zero at `0`, then
on a ball about `0` the discriminant has nonzero values arbitrarily close to every point. -/
theorem laneC_exists_weierstrassDiscr_ne_zero {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) (hD : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0) :
    ∃ ε > 0, ∀ z ∈ ball (0 : Fin n → ℂ) ε, ∀ δ > 0, ∃ z' ∈ ball z δ, weierstrassDiscr a z' ≠ 0 := by
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j => (ha j).eventually_analyticAt
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨ε, hε, fun z hz δ hδ => ?_⟩
  by_contra! H
  have hAn : AnalyticOnNhd ℂ (weierstrassDiscr a) (ball 0 ε) := fun z' hz' =>
    spec_analyticAt_weierstrassDiscr_aux (hεa z' hz')
  have hz0 : weierstrassDiscr a =ᶠ[𝓝 z] 0 :=
    Filter.mem_of_superset (ball_mem_nhds z hδ) fun z' hz' => H z' hz'
  have hEq := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ε).isPreconnected
    hz hz0
  exact hD (Filter.mem_of_superset (ball_mem_nhds 0 hε) fun z' hz' => hEq hz')

theorem spec_eventually_mem_closure_regular_monicInLast_aux {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (hD : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0) :
    ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), monicInLast a y = 0 →
      y ∈ closure {p | monicInLast a p = 0 ∧ deriv (fun w => monicInLast a (p.1, w)) p.2 ≠ 0} := by
  obtain ⟨ε, hε, hdense⟩ := laneC_exists_weierstrassDiscr_ne_zero ha hD
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j => (ha j).eventually_analyticAt
  have hfst : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), y.1 ∈ ball (0 : Fin n → ℂ) ε ∧
      ∀ j, AnalyticAt ℂ (a j) y.1 :=
    (continuous_fst.tendsto (0 : (Fin n → ℂ) × ℂ)).eventually
      (Filter.Eventually.and (ball_mem_nhds (0 : Fin n → ℂ) hε :
        ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ ball (0 : Fin n → ℂ) ε) hall)
  filter_upwards [hfst] with y hy hPy
  obtain ⟨z, w⟩ := y
  obtain ⟨hz, hza⟩ := hy
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨m, hm⟩ := laneC_order_monicInLast_natCast a z w
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : analyticOrderAt (fun w => monicInLast a (z, w)) w ≠ 0 :=
      analyticOrderAt_ne_zero.mpr
        ⟨(laneC_analyticAt_monicInLast hza w).comp₂ analyticAt_const analyticAt_id, hPy⟩
    exact this (by rw [hm]; rfl)
  obtain ⟨r', hr', hr'r, δ, hδ, -, -, hcount⟩ :=
    spec_exists_zeroCount_eq_order (laneC_analyticAt_monicInLast hza w) hm hr
  obtain ⟨z', hz', hD'⟩ := hdense z hz (min δ r) (lt_min hδ hr)
  have hc := hcount z' (ball_subset_ball (min_le_left _ _) hz')
  obtain ⟨w', hw', hw'0⟩ : ∃ w' ∈ ball w r',
      analyticOrderNatAt (fun w => monicInLast a (z', w)) w' ≠ 0 := by
    apply exists_ne_zero_of_finsum_mem_ne_zero
    rw [← zeroCount, hc]
    exact hm0
  have hne0 : analyticOrderAt (fun w => monicInLast a (z', w)) w' ≠ 0 := by
    intro h; exact hw'0 (by simp [analyticOrderNatAt, h])
  have hle := (spec_weierstrassDiscr_ne_zero_iff_aux a z').mp hD' w'
  have h1 : analyticOrderAt (fun w => monicInLast a (z', w)) w' = 1 := by
    generalize analyticOrderAt (fun w => monicInLast a (z', w)) w' = k at hne0 hle ⊢
    induction k using ENat.recTopCoe with
    | top => simp at hle
    | coe k => norm_cast at hne0 hle ⊢; omega
  refine ⟨(z', w'), ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero
    (f := fun w => monicInLast a (z', w)) hw'0,
    laneC_deriv_ne_zero_of_order_one (analyticOrderAt_ne_zero.mp hne0).1 h1⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨?_, ?_⟩
  · rw [dist_comm]; exact lt_of_lt_of_le (mem_ball.mp hz') (min_le_right _ _)
  · rw [dist_comm]; exact lt_trans (mem_ball.mp hw') hr'r

/-- Square-freeness transported along a linear automorphism and a unit factor: if
`f ∘ L = u · P` near `y`, `u` is analytic at `y` and `f` is square-free at `L y`, then `P` is
square-free at `y`. -/
theorem laneC_isSquareFreeAt_of_comp {f P u : (Fin n → ℂ) × ℂ → ℂ}
    (L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ)) {y : (Fin n → ℂ) × ℂ}
    (hf : IsSquareFreeAt f (L y)) (hu : AnalyticAt ℂ u y)
    (hfu : (fun p => f (L p)) =ᶠ[𝓝 y] fun p => u p * P p) : IsSquareFreeAt P y := by
  intro g h hg hh hg0 hP
  have hLs : ∀ {φ : (Fin n → ℂ) × ℂ → ℂ}, AnalyticAt ℂ φ y →
      AnalyticAt ℂ (fun q => φ (L.symm q)) (L y) := by
    intro φ hφ
    have : AnalyticAt ℂ φ (L.symm (L y)) := by simpa using hφ
    exact this.comp ((L.symm : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ)).analyticAt (L y))
  apply hf (fun q => g (L.symm q)) (fun q => u (L.symm q) * h (L.symm q)) (hLs hg)
    ((hLs hu).mul (hLs hh)) (by simpa using hg0)
  have hmem : {p | f (L p) = u p * P p ∧ P p = g p ^ 2 * h p} ∈ 𝓝 y := hfu.and hP
  have hcont : Tendsto L.symm (𝓝 (L y)) (𝓝 y) := by
    simpa using L.symm.continuous.tendsto (L y)
  filter_upwards [hcont hmem] with q hq
  obtain ⟨h1, h2⟩ := hq
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h1
  rw [h1, h2]
  ring

theorem spec_eventually_mem_closure_regular_aux {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hsq : ∀ᶠ y in 𝓝 0, IsSquareFreeAt f y) :
    ∀ᶠ y in 𝓝 0, f y = 0 → y ∈ closure {p | f p = 0 ∧ fderiv ℂ f p ≠ 0} := by
  have hnz : ¬ ∀ᶠ p in 𝓝 0, f p = 0 := by
    intro hz
    exact hsq.self_of_nhds 0 0 analyticAt_const analyticAt_const rfl
      (hz.mono fun p hp => by simp [hp])
  obtain ⟨m, -, L, u, hu, hu0, a, ha, hfu⟩ := spec_exists_linearEquiv_preparation_aux hf hnz
  have haa : ∀ j, AnalyticAt ℂ (a j) 0 := fun j => (ha j).1
  have hL0 : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto 0
  -- `P` is square-free near `0`
  have hsqP : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y := by
    filter_upwards [hL0 hsq, hu.eventually_analyticAt, hfu.eventually_nhds] with y h1 h2 h3
    exact laneC_isSquareFreeAt_of_comp L h1 h2 h3
  have hD := spec_weierstrassDiscr_not_eventually_zero_aux haa (fun j => (ha j).2) hsqP
  have hreg := spec_eventually_mem_closure_regular_monicInLast_aux haa hD
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j => (haa j).eventually_analyticAt
  have hall' : ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), ∀ j, AnalyticAt ℂ (a j) p.1 :=
    (continuous_fst.tendsto ((0 : (Fin n → ℂ) × ℂ))).eventually
      (p := fun z => ∀ j, AnalyticAt ℂ (a j) z) hall
  obtain ⟨V, hV, hVo, h0V⟩ := _root_.eventually_nhds_iff.mp
    ((((hfu.eventually_nhds.and (hu.continuousAt.eventually_ne hu0)).and
      hu.eventually_analyticAt).and hall').and hreg)
  have hLs : L.symm ⁻¹' V ∈ 𝓝 (0 : (Fin n → ℂ) × ℂ) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hVo.mem_nhds h0V)
  filter_upwards [hLs] with y hyV hy0
  set y' := L.symm y with hy'
  obtain ⟨⟨⟨⟨hF, hu'⟩, -⟩, -⟩, hreg'⟩ := hV y' hyV
  have hPy' : monicInLast a y' = 0 := by
    have h := hF.self_of_nhds
    simp only [hy', ContinuousLinearEquiv.apply_symm_apply, hy0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hu'
  have hcl := hreg' hPy'
  -- regular points of `P` in `V` map to regular points of `f`
  have hsub : L '' ({p | monicInLast a p = 0 ∧
      deriv (fun w => monicInLast a (p.1, w)) p.2 ≠ 0} ∩ V) ⊆
      {p | f p = 0 ∧ fderiv ℂ f p ≠ 0} := by
    rintro _ ⟨p, ⟨⟨hp0, hpd⟩, hpV⟩, rfl⟩
    obtain ⟨⟨⟨⟨hFp, hup⟩, hua⟩, hap⟩, -⟩ := hV p hpV
    have hG : AnalyticAt ℂ (fun q => u q * monicInLast a q) p := by
      have := laneC_analyticAt_monicInLast hap p.2
      exact hua.mul this
    refine ⟨by have h := hFp.self_of_nhds; simp only at h; rw [h, hp0, mul_zero],
      fun hfd => hpd ?_⟩
    -- `f = G ∘ L⁻¹` near `L p`
    have hfG : f =ᶠ[𝓝 (L p)] fun q => u (L.symm q) * monicInLast a (L.symm q) := by
      have hcont : Tendsto L.symm (𝓝 (L p)) (𝓝 p) := by
        simpa using L.symm.continuous.tendsto (L p)
      filter_upwards [hcont hFp] with q hq
      simpa using hq
    have hGd : HasFDerivAt (fun q => u q * monicInLast a q)
        (fderiv ℂ (fun q => u q * monicInLast a q) p) (L.symm (L p)) := by
      simpa using hG.differentiableAt.hasFDerivAt
    have hfd' := (hGd.comp (L p) L.symm.hasFDerivAt).congr_of_eventuallyEq hfG
    rw [hfd'.fderiv] at hfd
    have h01 : fderiv ℂ (fun q => u q * monicInLast a q) p (0, 1) = 0 := by
      have := congrArg (fun T : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ => T (L (0, 1))) hfd
      simpa using this
    -- the derivative along `(0, 1)`
    have hline : HasDerivAt (fun w : ℂ => ((p.1, w) : (Fin n → ℂ) × ℂ)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hGline : HasDerivAt (fun w => u (p.1, w) * monicInLast a (p.1, w))
        (fderiv ℂ (fun q => u q * monicInLast a q) p (0, 1)) p.2 := by
      exact hG.differentiableAt.hasFDerivAt.comp_hasDerivAt p.2 (by simpa using hline)
    have huline : HasDerivAt (fun w => u (p.1, w)) (deriv (fun w => u (p.1, w)) p.2) p.2 := by
      have hd : DifferentiableAt ℂ (fun w => u (p.1, w)) p.2 :=
        (hua.differentiableAt.comp p.2 (by simpa using hline.differentiableAt))
      exact hd.hasDerivAt
    have hPline : HasDerivAt (fun w => monicInLast a (p.1, w))
        (deriv (fun w => monicInLast a (p.1, w)) p.2) p.2 := by
      have hd : DifferentiableAt ℂ (fun w => monicInLast a (p.1, w)) p.2 :=
        ((laneC_analyticAt_monicInLast hap p.2).differentiableAt.comp p.2
          (by simpa using hline.differentiableAt))
      exact hd.hasDerivAt
    have huniq := hGline.unique (huline.mul hPline)
    rw [h01, hp0, mul_zero, zero_add] at huniq
    exact (mul_eq_zero.mp huniq.symm).resolve_left hup
  have hcl' : y' ∈ closure ({p | monicInLast a p = 0 ∧
      deriv (fun w => monicInLast a (p.1, w)) p.2 ≠ 0} ∩ V) := by
    rw [_root_.mem_closure_iff] at hcl ⊢
    intro o ho hyo
    obtain ⟨q, ⟨hqo, hqV⟩, hq⟩ := hcl (o ∩ V) (ho.inter hVo) ⟨hyo, hyV⟩
    exact ⟨q, hqo, hq, hqV⟩
  have : y = L y' := by simp [hy']
  rw [this]
  exact closure_mono hsub (image_closure_subset_closure_image L.continuous ⟨y', hcl', rfl⟩)

theorem spec_not_mem_closure_regular_sq_aux :
    (0 : (Fin n → ℂ) × ℂ) ∉
      closure {p | p.2 ^ 2 = 0 ∧ fderiv ℂ (fun q : (Fin n → ℂ) × ℂ => q.2 ^ 2) p ≠ 0} := by
  have : {p : (Fin n → ℂ) × ℂ | p.2 ^ 2 = 0 ∧
      fderiv ℂ (fun q : (Fin n → ℂ) × ℂ => q.2 ^ 2) p ≠ 0} = ∅ := by
    ext p
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hp
    have h2 : p.2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hp
    have hd : HasFDerivAt (fun q : (Fin n → ℂ) × ℂ => q.2 ^ 2)
        ((2 * p.2 ^ 1 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) p := by
      simpa using (hasFDerivAt_snd (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ) (p := p)).pow 2
    rw [hd.fderiv, h2]
    simp
  rw [this, closure_empty]
  exact notMem_empty _

end Regular

end HodgeLean.Foundations.AnalyticDivisorAlgebraic5
