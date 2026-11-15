import HodgeLean.Foundations.AnalyticDivisorAlgebraic18Defs

noncomputable section
open Filter Set Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic18

open AnalyticDivisorAlgebraic4 AnalyticDivisorAlgebraic5
open AnalyticDivisorAlgebraic6 AnalyticDivisorAlgebraic7 AnalyticDivisorAlgebraic11

private def gaga18_splitCoordinates (m : ℕ) :
    (Fin (m + 1) → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ℂ)).symm.trans
        (Equiv.prodComm _ _)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem gaga18_irreducible_prepared {m d : ℕ}
    (f u : (Fin m → ℂ) × ℂ → ℂ) (a : Fin d → (Fin m → ℂ) → ℂ)
    (hf : IsIrreducibleAt f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfac : f =ᶠ[𝓝 0] fun y ↦ u y * monicInLast a y) :
    IsIrreducibleAt (monicInLast a) 0 := by
  constructor
  · have := hf.1
    rw [hfac.self_of_nhds] at this
    exact (mul_eq_zero.mp this).resolve_left hu0
  · intro r s hr hs hrs
    have hurs : f =ᶠ[𝓝 0] fun y ↦ (u y * r y) * s y := by
      filter_upwards [hfac, hrs] with y hfy hry
      rw [hfy, hry, mul_assoc]
    rcases hf.2 (fun y ↦ u y * r y) s (hu.mul hr) hs hurs with hur | hs0
    · exact Or.inl fun hr0 ↦ hur (by simp [hr0])
    · exact Or.inr hs0

/-- Preparation in a regular last coordinate, including irreducibility of the prepared equation.
Source: Gunning--Rossi, II.B, Lemma 1 and Theorems 2--4;
`AnalyticDivisorAlgebraic6.spec_exists_linearChange_regular`, `spec_preparation_transfer`,
`spec_irreducible_transfer`; `AnalyticDivisorAlgebraic8.productAnalyticGermUFD`. -/
theorem gaga18_prepare_aux (n : ℕ) (p : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p) (hi : IsIrreducibleAt g p) :
    ∃ m : ℕ, ∃ L : (Fin n → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ),
    ∃ d : ℕ, 0 < d ∧ ∃ u : (Fin m → ℂ) × ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∃ a : Fin d → (Fin m → ℂ) → ℂ,
        (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
        analyticOrderAt (fun w : ℂ ↦ g (p + L.symm (0, w))) 0 = d ∧
        IsIrreducibleAt (monicInLast a) 0 ∧
        (fun y ↦ g (p + L.symm y)) =ᶠ[𝓝 0] fun y ↦ u y * monicInLast a y := by
  cases n with
  | zero =>
      exfalso
      have he : g =ᶠ[𝓝 p] fun _ ↦ (0 : ℂ) * 0 := Eventually.of_forall fun z ↦ by
        rw [Subsingleton.elim z p, zero_mul]
        exact hi.1
      rcases hi.2 (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const he with h | h
      · exact h rfl
      · exact h rfl
  | succ m =>
      let S := gaga18_splitCoordinates m
      let f : (Fin m → ℂ) × ℂ → ℂ := fun y ↦ g (p + S.symm y)
      have hT : AnalyticAt ℂ (fun y ↦ p + S.symm y) 0 :=
        analyticAt_const.add (S.symm.toContinuousLinearMap.analyticAt 0)
      have hf : AnalyticAt ℂ f 0 := hg.comp_of_eq hT (by simp [S])
      have hfi : IsIrreducibleAt f 0 := by
        constructor
        · simpa [f, S] using hi.1
        · intro r s hr hs hrs
          let r' : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ r (S (z - p))
          let s' : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ s (S (z - p))
          have hC : AnalyticAt ℂ (fun z ↦ S (z - p)) p :=
            (S.toContinuousLinearMap.analyticAt 0).comp_of_eq
              (analyticAt_id.sub analyticAt_const) (by simp)
          have hr' : AnalyticAt ℂ r' p := hr.comp_of_eq hC (by simp [S])
          have hs' : AnalyticAt ℂ s' p := hs.comp_of_eq hC (by simp [S])
          have hfac' : g =ᶠ[𝓝 p] fun z ↦ r' z * s' z := by
            have ht : Tendsto (fun z ↦ S (z - p)) (𝓝 p) (𝓝 0) := by
              simpa only [ContinuousAt, sub_self, map_zero] using hC.continuousAt
            filter_upwards [ht.eventually hrs] with z hz
            simpa [f, r', s'] using hz
          rcases hi.2 r' s' hr' hs' hfac' with hr0 | hs0
          · left
            simpa [r', S] using hr0
          · right
            simpa [s', S] using hs0
      have hfnz : ¬ ∀ᶠ y in 𝓝 0, f y = 0 := by
        intro hz
        rcases hfi.2 (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const
          (hz.mono fun y hy ↦ by simpa using hy) with h | h
        · exact h rfl
        · exact h rfl
      obtain ⟨d, _, A, u, hu, hu0, a, ha, hfac⟩ :=
        spec_exists_linearEquiv_preparation hf hfnz
      let L : (Fin (m + 1) → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ) := S.trans A.symm
      have hfiA : IsIrreducibleAt (fun y ↦ f (A y)) 0 := by
        constructor
        · simpa [f, S] using hi.1
        · intro r s hr hs hrs
          let r' := fun y ↦ r (A.symm y)
          let s' := fun y ↦ s (A.symm y)
          have hr' : AnalyticAt ℂ r' 0 := hr.comp_of_eq (A.symm.analyticAt 0) (by simp)
          have hs' : AnalyticAt ℂ s' 0 := hs.comp_of_eq (A.symm.analyticAt 0) (by simp)
          have hfacA : f =ᶠ[𝓝 0] fun y ↦ r' y * s' y := by
            have hct : ContinuousAt A.symm (0 : (Fin m → ℂ) × ℂ) :=
              A.symm.continuous.continuousAt
            have ht : Tendsto A.symm (𝓝 0) (𝓝 0) := by
              simpa only [ContinuousAt, map_zero] using hct
            filter_upwards [ht.eventually hrs] with y hy
            simpa [r', s'] using hy
          rcases hfi.2 r' s' hr' hs' hfacA with hr0 | hs0
          · left
            simpa [r'] using hr0
          · right
            simpa [s'] using hs0
      have hd0 : d ≠ 0 := by
        intro hd
        subst d
        have hm : monicInLast a = fun _ ↦ (1 : ℂ) := by
          funext y
          simp [monicInLast]
        have hirr := gaga18_irreducible_prepared _ _ _ hfiA hu hu0 hfac
        rw [hm] at hirr
        exact one_ne_zero hirr.1
      refine ⟨m, L, d, Nat.pos_of_ne_zero hd0, u, hu, hu0, a, ha, ?_,
        gaga18_irreducible_prepared _ _ _ hfiA hu hu0 hfac, ?_⟩
      · simpa [f, L, S] using
          spec_analyticOrderAt_of_preparation hu hu0 (fun j ↦ (ha j).2) hfac
      · simpa [f, L, S] using hfac

/-- An irreducible Weierstrass equation has a discriminant which is not the zero germ.
Source: Gunning--Rossi, II.B, Theorems 3--6; III.A, Theorem 1;
`AnalyticDivisorAlgebraic6.spec_irreducible_transfer`, `spec_eventually_isSquareFreeAt`,
`AnalyticDivisorAlgebraic5.spec_weierstrassDiscr_not_eventually_zero`. -/
theorem gaga18_discriminant_aux (m d : ℕ) (a : Fin d → (Fin m → ℂ) → ℂ)
    (hd : 0 < d) (ha : ∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0)
    (hi : IsIrreducibleAt (monicInLast a) 0) :
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 := by
  have hsq : IsSquareFreeAt (monicInLast a) 0 := by
    intro r s hr hs hr0 hfac
    have hfac' : monicInLast a =ᶠ[𝓝 0] fun y ↦ r y * (r y * s y) := by
      filter_upwards [hfac] with y hy
      simpa only [pow_two, mul_assoc] using hy
    rcases hi.2 r (fun y ↦ r y * s y) hr (hr.mul hs) hfac' with hrn | hrsn
    · exact hrn hr0
    · exact hrsn (by simp [hr0])
  exact spec_weierstrassDiscr_not_eventually_zero (fun j ↦ (ha j).1)
    (fun j ↦ (ha j).2)
    (spec_eventually_isSquareFreeAt
      (laneC_analyticAt_monicInLast (fun j ↦ (ha j).1) 0) hsq)

/-- Off the discriminant, all roots lie in the division neighbourhood and kill the remainder.
The displayed polynomial has degree below the divisor degree, hence is zero on these fibres.
Source: Gunning--Rossi, II.B, Theorems 3--4;
`AnalyticDivisorAlgebraic4.spec_weierstrass_division`, `spec_monicInLast_roots_small`;
`AnalyticDivisorAlgebraic5.spec_weierstrassDiscr_ne_zero_iff`. -/
theorem gaga18_remainder_roots_aux (m d : ℕ) (hd : 0 < d)
    (a b : Fin d → (Fin m → ℂ) → ℂ) (H q : (Fin m → ℂ) × ℂ → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0)
    (hb : ∀ j, AnalyticAt ℂ (b j) 0)
    (hH : AnalyticAt ℂ H 0) (hq : AnalyticAt ℂ q 0)
    (hdiv : H =ᶠ[𝓝 0] fun y ↦ q y * monicInLast a y + ∑ j, b j y.1 * y.2 ^ (j : ℕ))
    (hz : ∀ᶠ y in 𝓝 0, monicInLast a y = 0 → H y = 0) :
    ∀ᶠ z in 𝓝 0, weierstrassDiscr a z ≠ 0 →
      (∃ roots : Fin d → ℂ, Function.Injective roots ∧
        ∀ i, (monicPoly a z).eval (roots i) = 0 ∧
          (∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ)).eval (roots i) = 0) ∧
      (∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ)).degree < (d : WithBot ℕ) ∧
      ∀ j, b j z = 0 := by
  classical
  let R : (Fin m → ℂ) → Polynomial ℂ := fun z ↦
    ∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ)
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (hdiv.and hz)
  have hsmall := spec_monicInLast_roots_small
    (fun j ↦ (ha j).1.continuousAt) (fun j ↦ (ha j).2) hε
  have hanalytic : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j ↦ (ha j).1.eventually_analyticAt
  filter_upwards [hsmall, hanalytic, Metric.ball_mem_nhds (0 : Fin m → ℂ) hε] with z hs ha' hzε
  intro hΔ
  have hmul : ∀ w, (monicPoly a z).rootMultiplicity w ≤ 1 := fun w ↦ by
    have hle := (spec_weierstrassDiscr_ne_zero_iff a z).1 hΔ w
    rw [AnalyticDivisorAlgebraic5.gaga5b_analyticOrderAt_monicInLast_slice] at hle
    exact_mod_cast hle
  have hnodup : (monicPoly a z).roots.Nodup :=
    Multiset.nodup_iff_count_le_one.2 fun w ↦ by
      rw [Polynomial.count_roots]
      exact hmul w
  have hcard : (monicPoly a z).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree,
      (spec_monicPoly a z).2.1]
  let e : Fin d ≃ (monicPoly a z).roots.toFinset :=
    ((monicPoly a z).roots.toFinset.equivFinOfCardEq hcard).symm
  let roots : Fin d → ℂ := fun i ↦ (e i : ℂ)
  have hroots_inj : Function.Injective roots := fun i j hij ↦ by
    apply e.injective
    exact Subtype.ext hij
  have hroot : ∀ i, (monicPoly a z).eval (roots i) = 0 := fun i ↦ by
    exact (Polynomial.mem_roots (spec_monicPoly a z).1.ne_zero).mp
      (Multiset.mem_toFinset.mp (e i).property)
  have hrem : ∀ i, (R z).eval (roots i) = 0 := by
    intro i
    have hP : monicInLast a (z, roots i) = 0 := by
      rw [← (spec_monicPoly a z).2.2]
      exact hroot i
    have hwε : ‖roots i‖ < ε := hs (roots i) hP
    have hy : (z, roots i) ∈ Metric.ball (0 : (Fin m → ℂ) × ℂ) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      simpa only [Prod.fst_zero, Prod.snd_zero, dist_zero_right] using
        ⟨(by simpa only [dist_zero_right] using Metric.mem_ball.mp hzε), hwε⟩
    have hloc := hlocal _ hy
    have hHzero := hloc.1.symm.trans (hloc.2 hP)
    change q (z, roots i) * monicInLast a (z, roots i) +
      ∑ j, b j z * roots i ^ (j : ℕ) = 0 at hHzero
    rw [hP, mul_zero, zero_add] at hHzero
    rw [show R z = ∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ) by rfl]
    simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hHzero
  have hdegree : (R z).degree < (d : WithBot ℕ) := by
    exact Polynomial.degree_sum_fin_lt (fun j ↦ b j z)
  have hRzero : R z = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (R z) hroots_inj hrem
    simp only [Fintype.card_fin]
    by_cases hR : R z = 0
    · simp only [hR, Polynomial.natDegree_zero]
      exact hd
    · exact (Polynomial.natDegree_lt_iff_degree_lt hR).mpr hdegree
  have hbzero : ∀ j, b j z = 0 := by
    intro j
    have hc := congrArg (fun P : Polynomial ℂ ↦ P.coeff (j : ℕ)) hRzero
    simpa [R, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hc
  exact ⟨⟨roots, hroots_inj, fun i ↦ ⟨hroot i, hrem i⟩⟩, hdegree, hbzero⟩

/-- Identity-theorem extension of each analytic remainder coefficient across the discriminant.
Source: Gunning--Rossi, I.A, Theorem 6;
`AnalyticDivisorAlgebraic12.spec_germ_ne_zero_of_preconnected`. -/
theorem gaga18_extend_aux (m d : ℕ) (a b : Fin d → (Fin m → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) (hb : ∀ j, AnalyticAt ℂ (b j) 0)
    (hΔ : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0)
    (hoff : ∀ᶠ z in 𝓝 0, weierstrassDiscr a z ≠ 0 → ∀ j, b j z = 0) :
    ∀ᶠ z in 𝓝 0, ∀ j, b j z = 0 := by
  have haev : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), ∀ j, AnalyticAt ℂ (a j) z :=
    eventually_all.mpr fun j ↦ (ha j).eventually_analyticAt
  have hbev : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), ∀ j, AnalyticAt ℂ (b j) z :=
    eventually_all.mpr fun j ↦ (hb j).eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (haev.and (hbev.and hoff))
  have hfreq : ∃ᶠ z in 𝓝 (0 : Fin m → ℂ), weierstrassDiscr a z ≠ 0 :=
    Filter.not_eventually.mp hΔ
  obtain ⟨q, hqΔ, hqU⟩ := (hfreq.and_eventually (Metric.ball_mem_nhds 0 hε)).exists
  have hqdata := hball q hqU
  have hqΔev : ∀ᶠ z in 𝓝 q, weierstrassDiscr a z ≠ 0 :=
    (spec_analyticAt_weierstrassDiscr hqdata.1).continuousAt.eventually_ne hqΔ
  apply eventually_all.mpr
  intro j
  by_contra hj
  have hjne : @Filter.Germ.ofFun (Fin m → ℂ) ℂ (𝓝 0) (b j) ≠ 0 := by
    intro heq
    apply hj
    rw [← Filter.Germ.coe_zero] at heq
    exact Filter.Germ.coe_eq.mp heq
  have hjqne : @Filter.Germ.ofFun (Fin m → ℂ) ℂ (𝓝 q) (b j) ≠ 0 :=
    AnalyticDivisorAlgebraic12.spec_germ_ne_zero_of_preconnected (b j) (Metric.ball 0 ε)
      Metric.isOpen_ball (convex_ball 0 ε).isPreconnected
      (fun z hz ↦ (hball z hz).2.1 j) 0 q (Metric.mem_ball_self hε) hqU hjne
  apply hjqne
  change (↑(b j) : Filter.Germ (𝓝 q) ℂ) = ↑(0 : (Fin m → ℂ) → ℂ)
  rw [Filter.Germ.coe_eq]
  filter_upwards [Metric.isOpen_ball.mem_nhds hqU, hqΔev] with z hzU hzΔ
  exact (hball z hzU).2.2 hzΔ j

theorem spec_hypersurface_nullstellensatz_aux (n : ℕ) (p : Fin n → ℂ)
    (g h : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hgi : IsIrreducibleAt g p) (hz : ∀ᶠ z in 𝓝 p, g z = 0 → h z = 0) :
    ∃ c : (Fin n → ℂ) → ℂ, AnalyticAt ℂ c p ∧ h =ᶠ[𝓝 p] fun z ↦ g z * c z := by
  obtain ⟨m, L, d, hd, u, hu, hu0, a, ha, _, hi, hprep⟩ :=
    gaga18_prepare_aux n p g hg hgi
  have hT : AnalyticAt ℂ (fun y ↦ p + L.symm y) 0 :=
    analyticAt_const.add (L.symm.toContinuousLinearMap.analyticAt 0)
  have hT0 : p + L.symm 0 = p := by simp
  have hH : AnalyticAt ℂ (fun y ↦ h (p + L.symm y)) 0 :=
    (hh.comp_of_eq hT hT0)
  obtain ⟨q, hq, b, hb, hdiv⟩ := spec_weierstrass_division hH
    (fun j ↦ (ha j).1) (fun j ↦ (ha j).2)
  have hz' : ∀ᶠ y in 𝓝 0, monicInLast a y = 0 → h (p + L.symm y) = 0 := by
    have ht : Tendsto (fun y ↦ p + L.symm y) (𝓝 0) (𝓝 p) :=
      by simpa only [ContinuousAt, map_zero, add_zero] using hT.continuousAt
    filter_upwards [ht.eventually hz, hprep] with y hy hp
    intro hy0
    apply hy
    rw [hp, hy0, mul_zero]
  have hr := gaga18_remainder_roots_aux m d hd a b _ q ha hb hH hq hdiv hz'
  have hb0 := gaga18_extend_aux m d a b (fun j ↦ (ha j).1) hb
    (gaga18_discriminant_aux m d a hd ha hi) (hr.mono fun _ hz ↦ fun hΔ ↦ (hz hΔ).2.2)
  have he : ∀ᶠ y in 𝓝 0, h (p + L.symm y) = g (p + L.symm y) * (q y / u y) := by
    have hb' := (continuous_fst.tendsto (0 : (Fin m → ℂ) × ℂ)).eventually hb0
    filter_upwards [hdiv, hprep, hb', hu.continuousAt.eventually_ne hu0] with y hdiv hprep hb hy
    rw [hdiv, hprep]
    simp only [hb, zero_mul, Finset.sum_const_zero, add_zero]
    field_simp
  have hS : AnalyticAt ℂ (fun z ↦ L (z - p)) p :=
    (L.toContinuousLinearMap.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hS0 : L (p - p) = 0 := by simp
  refine ⟨fun z ↦ q (L (z - p)) / u (L (z - p)),
    (hq.div hu hu0).comp_of_eq hS hS0, ?_⟩
  have ht : Tendsto (fun z ↦ L (z - p)) (𝓝 p) (𝓝 0) := by simpa only [ContinuousAt, sub_self, map_zero] using hS.continuousAt
  filter_upwards [ht.eventually he] with z hz
  simpa only [L.symm_apply_apply, add_sub_cancel] using hz

theorem spec_reduced_zero_germs_associated_aux (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfr : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p := by
  classical
  obtain ⟨e, -, -⟩ := AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n p
  letI : UniqueFactorizationMonoid (AnalyticGermAt n p) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid
      (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)
  letI : StrongNormalizationMonoid (AnalyticGermAt n p) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let F : AnalyticGermAt n p := ⟨Filter.Germ.ofFun f, f, hf, rfl⟩
  let G : AnalyticGermAt n p := ⟨Filter.Germ.ofFun g, g, hg, rfl⟩
  have irreducibleAt_of_irreducibleGerm (A : AnalyticGermAt n p)
      (hA : Irreducible A) :
      ∃ a : (Fin n → ℂ) → ℂ, ∃ ha : AnalyticAt ℂ a p,
        A = ⟨Filter.Germ.ofFun a, a, ha, rfl⟩ ∧ IsIrreducibleAt a p := by
    obtain ⟨a, ha, har⟩ := A.2
    have hAr : A = ⟨Filter.Germ.ofFun a, a, ha, rfl⟩ := Subtype.ext har.symm
    subst A
    refine ⟨a, ha, rfl, ?_⟩
    constructor
    · by_contra hap
      apply hA.not_isUnit
      apply isUnit_iff_exists_inv.mpr
      let B : AnalyticGermAt n p :=
        ⟨Filter.Germ.ofFun (fun z ↦ (a z)⁻¹), fun z ↦ (a z)⁻¹, ha.inv hap, rfl⟩
      refine ⟨B, Subtype.ext ?_⟩
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [ha.continuousAt.eventually_ne hap] with z hz
      exact mul_inv_cancel₀ hz
    · intro b c hb hc hfac
      let B : AnalyticGermAt n p := ⟨Filter.Germ.ofFun b, b, hb, rfl⟩
      let C : AnalyticGermAt n p := ⟨Filter.Germ.ofFun c, c, hc, rfl⟩
      have hAC : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) = B * C := by
        apply Subtype.ext
        exact Filter.Germ.coe_eq.mpr hfac
      rcases hA.isUnit_or_isUnit hAC with hB | hC
      · left
        intro hbp
        exact (hB.map (analyticGermAtValue n p)).ne_zero
          (by change (Filter.Germ.ofFun b).value = 0
              rw [Filter.Germ.value_ofFun, hbp])
      · right
        intro hcp
        exact (hC.map (analyticGermAtValue n p)).ne_zero
          (by change (Filter.Germ.ofFun c).value = 0
              rw [Filter.Germ.value_ofFun, hcp])
  have factor_dvd (a b c : (Fin n → ℂ) → ℂ) (ha : AnalyticAt ℂ a p)
      (hb : AnalyticAt ℂ b p) (hc : AnalyticAt ℂ c p) (hai : IsIrreducibleAt a p)
      (hab : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) ∣
        ⟨Filter.Germ.ofFun b, b, hb, rfl⟩)
      (hzab : ∀ᶠ z in 𝓝 p, b z = 0 → c z = 0) :
      (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) ∣
        ⟨Filter.Germ.ofFun c, c, hc, rfl⟩ := by
    obtain ⟨C, hC⟩ := hab
    obtain ⟨d, hd, hdr⟩ := C.2
    have hba : ∀ᶠ z in 𝓝 p, a z = 0 → b z = 0 := by
      have he : ∀ᶠ z in 𝓝 p, b z = a z * d z := by
        apply Filter.Germ.coe_eq.mp
        have := congrArg Subtype.val hC
        calc
          Filter.Germ.ofFun b = (⟨Filter.Germ.ofFun b, b, hb, rfl⟩ : AnalyticGermAt n p).1 := rfl
          _ = (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ * C).1 := this
          _ = (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p).1 * C.1 := rfl
          _ = Filter.Germ.ofFun a * Filter.Germ.ofFun d := congrArg₂ (· * ·) rfl hdr.symm
          _ = Filter.Germ.ofFun (fun z ↦ a z * d z) := rfl
      filter_upwards [he] with z hez haz
      rw [hez, haz, zero_mul]
    have hac : ∀ᶠ z in 𝓝 p, a z = 0 → c z = 0 := by
      filter_upwards [hba, hzab] with z hab hbc
      exact fun haz ↦ hbc (hab haz)
    obtain ⟨q, hq, hqfac⟩ := spec_hypersurface_nullstellensatz_aux n p a c ha hc hai hac
    refine ⟨⟨Filter.Germ.ofFun q, q, hq, rfl⟩, Subtype.ext ?_⟩
    exact Filter.Germ.coe_eq.mpr hqfac
  have hF0 : F ≠ 0 := hfr.ne_zero
  have hG0 : G ≠ 0 := hgr.ne_zero
  have hmem : ∀ x, x ∈ UniqueFactorizationMonoid.normalizedFactors F ↔
      x ∈ UniqueFactorizationMonoid.normalizedFactors G := by
    intro x
    constructor
    · intro hx
      have hxi := UniqueFactorizationMonoid.irreducible_of_normalized_factor x hx
      obtain ⟨a, ha, rfl, hai⟩ := irreducibleAt_of_irreducibleGerm x hxi
      have hdF : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) ∣ F :=
        Multiset.dvd_prod hx |>.trans
          (UniqueFactorizationMonoid.prod_normalizedFactors hF0).dvd
      have hdG := factor_dvd a f g ha hf hg hai hdF (hz.mono fun _ h ↦ h.mp)
      obtain ⟨y, hy, hxy⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hG0 hxi hdG
      have hnx := UniqueFactorizationMonoid.normalize_normalized_factor _ hx
      have hny := UniqueFactorizationMonoid.normalize_normalized_factor _ hy
      have heq : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) = y := calc
        (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) =
            normalize (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) := hnx.symm
        _ = normalize y := normalize_eq_normalize hxy.dvd hxy.symm.dvd
        _ = y := hny
      simpa only [heq] using hy
    · intro hx
      have hxi := UniqueFactorizationMonoid.irreducible_of_normalized_factor x hx
      obtain ⟨a, ha, rfl, hai⟩ := irreducibleAt_of_irreducibleGerm x hxi
      have hdG : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) ∣ G :=
        Multiset.dvd_prod hx |>.trans
          (UniqueFactorizationMonoid.prod_normalizedFactors hG0).dvd
      have hdF : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) ∣ F := by
        apply factor_dvd a g f ha hg hf hai hdG
        exact hz.mono fun _ h ↦ h.mpr
      obtain ⟨y, hy, hxy⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hF0 hxi hdF
      have hnx := UniqueFactorizationMonoid.normalize_normalized_factor _ hx
      have hny := UniqueFactorizationMonoid.normalize_normalized_factor _ hy
      have heq : (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) = y := calc
        (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) =
            normalize (⟨Filter.Germ.ofFun a, a, ha, rfl⟩ : AnalyticGermAt n p) := hnx.symm
        _ = normalize y := normalize_eq_normalize hxy.dvd hxy.symm.dvd
        _ = y := hny
      simpa only [heq] using hy
  have hfac : UniqueFactorizationMonoid.normalizedFactors F =
      UniqueFactorizationMonoid.normalizedFactors G := by
    apply Multiset.ext.mpr
    intro x
    by_cases hx : x ∈ UniqueFactorizationMonoid.normalizedFactors F
    · rw [Multiset.count_eq_one_of_mem
          ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hF0).mp hfr) hx,
        Multiset.count_eq_one_of_mem
          ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hG0).mp hgr)
          ((hmem x).mp hx)]
    · rw [Multiset.count_eq_zero.mpr hx, Multiset.count_eq_zero.mpr (mt (hmem x).mpr hx)]
  have hp : Associated (UniqueFactorizationMonoid.normalizedFactors F).prod
      (UniqueFactorizationMonoid.normalizedFactors G).prod := hfac ▸ Associated.refl _
  have hassoc : Associated F G :=
    (UniqueFactorizationMonoid.prod_normalizedFactors hF0).symm.trans
      (hp.trans (UniqueFactorizationMonoid.prod_normalizedFactors hG0))
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨q, hq, hqu⟩ := (u : AnalyticGermAt n p).2
  refine ⟨q, hq, ?_, ?_⟩
  · have huv := u.isUnit.map (analyticGermAtValue n p)
    have hv : analyticGermAtValue n p (u : AnalyticGermAt n p) = q p := by
      change (u : AnalyticGermAt n p).1.value = q p
      rw [← hqu, Filter.Germ.value_ofFun]
    exact hv ▸ huv.ne_zero
  · apply Filter.Germ.coe_eq.mp
    have := congrArg Subtype.val hu
    calc
      Filter.Germ.ofFun f = F.1 := rfl
      _ = (G * (u : AnalyticGermAt n p)).1 := this.symm
      _ = G.1 * (u : AnalyticGermAt n p).1 := rfl
      _ = Filter.Germ.ofFun g * Filter.Germ.ofFun q := by rw [hqu]
      _ = Filter.Germ.ofFun (fun x ↦ q x * g x) := by rw [mul_comm]; rfl

private theorem germ_isUnit_of_value_ne {n : ℕ} {p : Fin n → ℂ}
    (x : AnalyticGermAt n p) (hx : analyticGermAtValue n p x ≠ 0) : IsUnit x := by
  obtain ⟨f, hf, hfx⟩ := x.2
  have hfp : f p ≠ 0 := by
    change x.1.value ≠ 0 at hx
    rw [← hfx] at hx
    simpa using hx
  let y : AnalyticGermAt n p := ⟨↑(fun z ↦ (f z)⁻¹), fun z ↦ (f z)⁻¹, hf.inv hfp, rfl⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change x.1 * y.1 = 1
  rw [← hfx]
  exact Filter.Germ.coe_eq.mpr <| (hf.continuousAt.eventually_ne hfp).mono fun z hz ↦
    mul_inv_cancel₀ hz

private theorem germ_irreducible_of_at {n : ℕ} {p : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) (hi : IsIrreducibleAt f p) :
    Irreducible (⟨↑f, f, hf, rfl⟩ : AnalyticGermAt n p) := by
  constructor
  · intro hu
    exact (hu.map (analyticGermAtValue n p)).ne_zero hi.1
  · intro a b hab
    obtain ⟨A, hA, ha⟩ := a.2
    obtain ⟨B, hB, hb⟩ := b.2
    have he : f =ᶠ[𝓝 p] fun z ↦ A z * B z := by
      apply Filter.Germ.coe_eq.mp
      calc
        ↑f = (⟨↑f, f, hf, rfl⟩ : AnalyticGermAt n p).1 := rfl
        _ = (a * b).1 := congrArg Subtype.val hab
        _ = a.1 * b.1 := rfl
        _ = ↑A * ↑B := congrArg₂ (· * ·) ha.symm hb.symm
        _ = ↑(fun z ↦ A z * B z) := rfl
    rcases hi.2 A B hA hB he with h | h
    · left
      apply germ_isUnit_of_value_ne a
      have hv := congrArg (fun t : Filter.Germ (𝓝 p) ℂ ↦ t.value) ha
      change a.1.value ≠ 0
      rw [← hv]
      simpa using h
    · right
      apply germ_isUnit_of_value_ne b
      have hv := congrArg (fun t : Filter.Germ (𝓝 p) ℂ ↦ t.value) hb
      change b.1.value ≠ 0
      rw [← hv]
      simpa using h

private theorem squareFreeAt_mul_of_irreducible_coprime {n : ℕ} {p : Fin n → ℂ}
    {F G : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p) (hc : IsCoprimeAt F G p) :
    IsSquareFreeAt (fun z ↦ F z * G z) p := by
  obtain ⟨e, -⟩ := AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n p
  letI : UniqueFactorizationMonoid (AnalyticGermAt n p) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid (spec_analyticGerm_ufd n)
  let f : AnalyticGermAt n p := ⟨↑F, F, hF, rfl⟩
  let g : AnalyticGermAt n p := ⟨↑G, G, hG, rfl⟩
  have hfi : Irreducible f := germ_irreducible_of_at hF hiF
  have hgi : Irreducible g := germ_irreducible_of_at hG hiG
  have hnfd : ¬ f ∣ g := by
    rintro ⟨c, hcEq⟩
    obtain ⟨C, hC, hcC⟩ := c.2
    apply hc
    refine ⟨F, fun _ ↦ 1, C, hF, analyticAt_const, hC, hiF.1, ?_, ?_⟩
    · exact Eventually.of_forall fun z ↦ by simp
    · apply Filter.Germ.coe_eq.mp
      calc
        ↑G = g.1 := rfl
        _ = (f * c).1 := congrArg Subtype.val hcEq
        _ = f.1 * c.1 := rfl
        _ = ↑F * ↑C := congrArg₂ (· * ·) rfl hcC.symm
        _ = ↑(fun z ↦ F z * C z) := rfl
  have hsf : Squarefree (f * g) := squarefree_mul_iff.mpr
    ⟨hfi.isRelPrime_iff_not_dvd.mpr hnfd, hfi.squarefree, hgi.squarefree⟩
  intro A B hA hB hA0 hfac
  let a : AnalyticGermAt n p := ⟨↑A, A, hA, rfl⟩
  let b : AnalyticGermAt n p := ⟨↑B, B, hB, rfl⟩
  have hadvd : a * a ∣ f * g := by
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr (hfac.mono fun z hz ↦ by simpa [pow_two, mul_assoc] using hz)
  have hau := hsf a hadvd
  exact (hau.map (analyticGermAtValue n p)).ne_zero hA0

private def laneD_splitCoordinates (m : ℕ) :
    (Fin (m + 1) → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ℂ)).symm.trans
        (Equiv.prodComm _ _)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem eventually_squareFreeAt_finSucc {m : ℕ} {p : Fin (m + 1) → ℂ}
    {f : (Fin (m + 1) → ℂ) → ℂ} (hf : AnalyticAt ℂ f p)
    (hsf : IsSquareFreeAt f p) : ∀ᶠ q in 𝓝 p, IsSquareFreeAt f q := by
  let L := laneD_splitCoordinates m
  let T : ((Fin m → ℂ) × ℂ) → (Fin (m + 1) → ℂ) := fun y ↦ p + L.symm y
  have hT (y) : AnalyticAt ℂ T y := analyticAt_const.add (L.symm.analyticAt y)
  have hfT : AnalyticAt ℂ (fun y ↦ f (T y)) 0 := by
    exact hf.comp_of_eq (hT 0) (by simp [T])
  have hsfT : IsSquareFreeAt (fun y ↦ f (T y)) 0 := by
    intro a b ha hb ha0 hab
    let A : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ a (L (z - p))
    let B : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ b (L (z - p))
    have hS : AnalyticAt ℂ (fun z ↦ L (z - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    apply hsf A B (ha.comp_of_eq hS (by simp)) (hb.comp_of_eq hS (by simp))
      (by simp [A, ha0])
    have ht : Tendsto (fun z ↦ L (z - p)) (𝓝 p) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, map_zero] using hS.continuousAt
    filter_upwards [ht.eventually hab] with z hz
    simpa [T, A, B] using hz
  have hnear := spec_eventually_isSquareFreeAt hfT hsfT
  have hS : Tendsto (fun q : Fin (m + 1) → ℂ ↦ L (q - p)) (𝓝 p) (𝓝 0) := by
    have ha : AnalyticAt ℂ (fun q ↦ L (q - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    simpa only [ContinuousAt, sub_self, map_zero] using ha.continuousAt
  filter_upwards [hS.eventually hnear] with q hq
  intro A B hA hB hA0 hab
  let a : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ A (T y)
  let b : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ B (T y)
  have hqT : T (L (q - p)) = q := by simp [T]
  apply hq a b (hA.comp_of_eq (hT _) hqT) (hB.comp_of_eq (hT _) hqT)
    (by change A (T (L (q - p))) = 0; rw [hqT, hA0])
  have ht : Tendsto T (𝓝 (L (q - p))) (𝓝 q) := by
    simpa only [ContinuousAt, hqT] using (hT (L (q - p))).continuousAt
  filter_upwards [ht.eventually hab] with y hy
  simpa [a, b] using hy

/-- Coprimality propagates for one pair. The selected-factor decompositions at `q` are
quantified separately; their irreducible factors cannot match across the two groups.
Source: Gunning--Rossi, II.B, Theorems 3--6 and III.A, Theorem 1;
`AnalyticDivisorAlgebraic14.spec_exists_irreducible_decomposition_at`,
`AnalyticDivisorAlgebraic17.spec_nearby_factor_matching`,
`AnalyticDivisorAlgebraic7.spec_irreducible_decomposition_unique`,
`spec_hypersurface_nullstellensatz_aux`. -/
theorem gaga18_pair_propagation_aux (n : ℕ) (p : Fin n → ℂ)
    (F G : (Fin n → ℂ) → ℂ) (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p)
    (hc : IsCoprimeAt F G p) :
    ∀ᶠ q in 𝓝 p, IsCoprimeAt F G q ∧
      ∀ (k l : ℕ) (u v : (Fin n → ℂ) → ℂ)
        (Q : Fin k → (Fin n → ℂ) → ℂ) (R : Fin l → (Fin n → ℂ) → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (F =ᶠ[𝓝 q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (G =ᶠ[𝓝 q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q := by
  have hsq := squareFreeAt_mul_of_irreducible_coprime hF hG hiF hiG hc
  have hnear : ∀ᶠ q in 𝓝 p, IsSquareFreeAt (fun z ↦ F z * G z) q := by
    cases n with
    | zero => filter_upwards [] with q; simpa [Subsingleton.elim q p] using hsq
    | succ m => exact eventually_squareFreeAt_finSucc (hF.mul hG) hsq
  filter_upwards [hnear, hF.eventually_analyticAt, hG.eventually_analyticAt] with q hsq hFq hGq
  have hcq : IsCoprimeAt F G q := by
    rintro ⟨A, s, t, hA, hs, ht, hA0, hFs, hGt⟩
    apply hsq A (fun z ↦ s z * t z) hA (hs.mul ht) hA0
    filter_upwards [hFs, hGt] with z hzF hzG
    rw [hzF, hzG]
    ring
  refine ⟨hcq, ?_⟩
  intro k l u v Q R d e hu _ hv _ hQ hR _ _ hfacF hfacG j j' hassoc
  let fg : AnalyticGermAt n q := ⟨↑F, F, hFq, rfl⟩
  let gg : AnalyticGermAt n q := ⟨↑G, G, hGq, rfl⟩
  let ug : AnalyticGermAt n q := ⟨↑u, u, hu, rfl⟩
  let vg : AnalyticGermAt n q := ⟨↑v, v, hv, rfl⟩
  let qg (i : Fin k) : AnalyticGermAt n q := ⟨↑(Q i), Q i, (hQ i).1, rfl⟩
  let rg (i : Fin l) : AnalyticGermAt n q := ⟨↑(R i), R i, (hR i).1, rfl⟩
  have hprodF : (↑(fun z ↦ ∏ i, Q i z ^ d i) : Filter.Germ (𝓝 q) ℂ) =
      ∏ i, (↑(Q i) : Filter.Germ (𝓝 q) ℂ) ^ d i := by
    classical
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _ ↦ rfl)
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        calc
          (↑(fun z ↦ ∏ i ∈ insert a s, Q i z ^ d i) : Filter.Germ (𝓝 q) ℂ) =
              ↑(fun z ↦ Q a z ^ d a * ∏ i ∈ s, Q i z ^ d i) := by
                congr 1; funext z; rw [Finset.prod_insert ha]
          _ = (↑(Q a) : Filter.Germ (𝓝 q) ℂ) ^ d a *
              ↑(fun z ↦ ∏ i ∈ s, Q i z ^ d i) :=
                Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _ ↦ rfl)
          _ = _ := congrArg ((↑(Q a) : Filter.Germ (𝓝 q) ℂ) ^ d a * ·) ih
  have hprodG : (↑(fun z ↦ ∏ i, R i z ^ e i) : Filter.Germ (𝓝 q) ℂ) =
      ∏ i, (↑(R i) : Filter.Germ (𝓝 q) ℂ) ^ e i := by
    classical
    induction (Finset.univ : Finset (Fin l)) using Finset.induction_on with
    | empty => exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _ ↦ rfl)
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        calc
          (↑(fun z ↦ ∏ i ∈ insert a s, R i z ^ e i) : Filter.Germ (𝓝 q) ℂ) =
              ↑(fun z ↦ R a z ^ e a * ∏ i ∈ s, R i z ^ e i) := by
                congr 1; funext z; rw [Finset.prod_insert ha]
          _ = (↑(R a) : Filter.Germ (𝓝 q) ℂ) ^ e a *
              ↑(fun z ↦ ∏ i ∈ s, R i z ^ e i) :=
                Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _ ↦ rfl)
          _ = _ := congrArg ((↑(R a) : Filter.Germ (𝓝 q) ℂ) ^ e a * ·) ih
  have heqF : fg = ug * ∏ i, qg i ^ d i := by
    apply Subtype.ext
    calc
      fg.1 = ↑F := rfl
      _ = ↑(fun z ↦ u z * ∏ i, Q i z ^ d i) := Filter.Germ.coe_eq.mpr hfacF
      _ = (↑u : Filter.Germ (𝓝 q) ℂ) * ↑(fun z ↦ ∏ i, Q i z ^ d i) := rfl
      _ = (↑u : Filter.Germ (𝓝 q) ℂ) * ∏ i, (↑(Q i) : Filter.Germ (𝓝 q) ℂ) ^ d i :=
        congrArg ((↑u : Filter.Germ (𝓝 q) ℂ) * ·) hprodF
      _ = ug.1 * ∏ i, (qg i).1 ^ d i := rfl
      _ = (ug * ∏ i, qg i ^ d i).1 := by simp
  have heqG : gg = vg * ∏ i, rg i ^ e i := by
    apply Subtype.ext
    calc
      gg.1 = ↑G := rfl
      _ = ↑(fun z ↦ v z * ∏ i, R i z ^ e i) := Filter.Germ.coe_eq.mpr hfacG
      _ = (↑v : Filter.Germ (𝓝 q) ℂ) * ↑(fun z ↦ ∏ i, R i z ^ e i) := rfl
      _ = (↑v : Filter.Germ (𝓝 q) ℂ) * ∏ i, (↑(R i) : Filter.Germ (𝓝 q) ℂ) ^ e i :=
        congrArg ((↑v : Filter.Germ (𝓝 q) ℂ) * ·) hprodG
      _ = vg.1 * ∏ i, (rg i).1 ^ e i := rfl
      _ = (vg * ∏ i, rg i ^ e i).1 := by simp
  have hqdivF : qg j ∣ fg := by
    rw [heqF]
    exact dvd_trans (dvd_pow_self _ (Nat.ne_of_gt (hQ j).2.2))
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i ↦ qg i ^ d i)
        (Finset.mem_univ j)) ug)
  have hrdivG : rg j' ∣ gg := by
    rw [heqG]
    exact dvd_trans (dvd_pow_self _ (Nat.ne_of_gt (hR j').2.2))
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i ↦ rg i ^ e i)
        (Finset.mem_univ j')) vg)
  obtain ⟨w, hw, hw0, hQR⟩ := hassoc
  let wg : AnalyticGermAt n q := ⟨↑w, w, hw, rfl⟩
  have hwu : IsUnit wg := germ_isUnit_of_value_ne wg (by
    change wg.1.value ≠ 0
    simpa [wg] using hw0)
  have hqreq : qg j = wg * rg j' := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr hQR
  have hassoc : Associated (qg j) (rg j') := by
    rw [hqreq]
    exact associated_unit_mul_left _ _ hwu
  have hqdivG : qg j ∣ gg := hassoc.dvd_iff_dvd_left.mpr hrdivG
  obtain ⟨cf, hcf⟩ := hqdivF
  obtain ⟨cg, hcg⟩ := hqdivG
  obtain ⟨CF, hCF, hcfrep⟩ := cf.2
  obtain ⟨CG, hCG, hcgrep⟩ := cg.2
  apply hcq
  refine ⟨Q j, CF, CG, (hQ j).1, hCF, hCG, (hQ j).2.1.1, ?_, ?_⟩
  · apply Filter.Germ.coe_eq.mp
    calc
      ↑F = fg.1 := rfl
      _ = (qg j * cf).1 := congrArg Subtype.val hcf
      _ = (qg j).1 * cf.1 := rfl
      _ = ↑(Q j) * ↑CF := congrArg₂ (· * ·) rfl hcfrep.symm
      _ = ↑(fun z ↦ Q j z * CF z) := rfl
  · apply Filter.Germ.coe_eq.mp
    calc
      ↑G = gg.1 := rfl
      _ = (qg j * cg).1 := congrArg Subtype.val hcg
      _ = (qg j).1 * cg.1 := rfl
      _ = ↑(Q j) * ↑CG := congrArg₂ (· * ·) rfl hcgrep.symm
      _ = ↑(fun z ↦ Q j z * CG z) := rfl

theorem spec_eventually_pairwise_coprime_aux (n r : ℕ) (p : Fin n → ℂ)
    (P : Fin r → (Fin n → ℂ) → ℂ) (hP : ∀ a, AnalyticAt ℂ (P a) p)
    (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hcP : Pairwise (fun a b ↦ IsCoprimeAt (P a) (P b) p)) :
    ∃ N, IsOpen N ∧ p ∈ N ∧ ∀ q ∈ N, ∀ a b, a ≠ b →
      ¬ ∃ A s t : (Fin n → ℂ) → ℂ, AnalyticAt ℂ A q ∧ IsIrreducibleAt A q ∧
        AnalyticAt ℂ s q ∧ (P a =ᶠ[𝓝 q] fun z ↦ A z * s z) ∧
        AnalyticAt ℂ t q ∧ (P b =ᶠ[𝓝 q] fun z ↦ A z * t z) := by
  have hpairs : ∀ a b, ∀ᶠ q in 𝓝 p, a ≠ b → IsCoprimeAt (P a) (P b) q := by
    intro a b
    by_cases hab : a = b
    · exact Eventually.of_forall fun _ hne ↦ False.elim (hne hab)
    · exact (gaga18_pair_propagation_aux n p (P a) (P b) (hP a) (hP b)
        (hiP a) (hiP b) (hcP hab)).mono fun _ h _ ↦ h.1
  have hall : ∀ᶠ q in 𝓝 p, ∀ a b, a ≠ b → IsCoprimeAt (P a) (P b) q :=
    eventually_all.mpr fun a ↦ eventually_all.mpr (hpairs a)
  obtain ⟨N, hNsub, hNo, hpN⟩ := mem_nhds_iff.mp hall
  refine ⟨N, hNo, hpN, ?_⟩
  intro q hq a b hab hcommon
  obtain ⟨A, s, t, hA, hiA, hs, hAs, ht, hAt⟩ := hcommon
  exact hNsub hq a b hab ⟨A, s, t, hA, hs, ht, hiA.1, hAs, hAt⟩

/-- The two coordinate factors of the crossing, with coprimality at the origin.
Source: Gunning--Rossi, II.B, Theorems 3--6;
`AnalyticDivisorAlgebraic17.gaga17_crossing_data`, transported to `Fin 2` coordinates. -/
private theorem gaga18_irreducibleAt_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} (hf : AnalyticAt ℂ f y) (hf0 : f y = 0)
    (hd : fderiv ℂ f y ≠ 0) : IsIrreducibleAt f y := by
  refine ⟨hf0, ?_⟩
  intro g h hg hh hfac
  by_contra hn
  push Not at hn
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have he0 : fderiv ℂ (fun x ↦ g x * h x) y = 0 := by
    change fderiv ℂ (g * h) y = 0
    rw [fderiv_mul hg.differentiableAt hh.differentiableAt, hn.1, hn.2]
    ext z
    simp
  exact hd (he.trans he0)

private theorem gaga18_fderiv_coord_ne_zero (i : Fin 2) :
    fderiv ℂ (fun z : Fin 2 → ℂ ↦ z i) 0 ≠ 0 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z i)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) i) 0 := by fun_prop
  intro h
  have he := congrArg (fun L ↦ L (Pi.single i 1)) h
  rw [hd.fderiv] at he
  simp [ContinuousLinearMap.proj_apply] at he

private theorem gaga18_coordinate_coprime :
    IsCoprimeAt (fun z : Fin 2 → ℂ ↦ z 0) (fun z ↦ z 1) 0 := by
  rintro ⟨q, r, s, hq, hr, hs, hq0, hfr, hfs⟩
  have hfr' := hfr.fderiv_eq (𝕜 := ℂ)
  have hfs' := hfs.fderiv_eq (𝕜 := ℂ)
  have hmulr := fderiv_mul hq.differentiableAt hr.differentiableAt
  have hmuls := fderiv_mul hq.differentiableAt hs.differentiableAt
  change fderiv ℂ (fun x ↦ q x * r x) 0 = _ at hmulr
  change fderiv ℂ (fun x ↦ q x * s x) 0 = _ at hmuls
  have hd0 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 0)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0) 0 := by fun_prop
  have hd1 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) 0 := by fun_prop
  have er0 := congrArg (fun L ↦ L (Pi.single 0 1)) hfr'
  have er1 := congrArg (fun L ↦ L (Pi.single 1 1)) hfr'
  have es0 := congrArg (fun L ↦ L (Pi.single 0 1)) hfs'
  have es1 := congrArg (fun L ↦ L (Pi.single 1 1)) hfs'
  rw [hd0.fderiv, hmulr, hq0] at er0 er1
  rw [hd1.fderiv, hmuls, hq0] at es0 es1
  norm_num [ContinuousLinearMap.proj_apply] at er0 er1 es0 es1
  have hr0 : r 0 ≠ 0 := by
    intro hrz
    rw [hrz, zero_mul] at er0
    exact one_ne_zero er0
  have hdq1 : fderiv ℂ q 0 (Pi.single 1 1) = 0 := er1.resolve_left hr0
  rw [hdq1, mul_zero] at es1
  exact one_ne_zero es1

theorem gaga18_coordinate_data_aux :
    (∀ i : Fin 2, AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z i) 0 ∧
      IsIrreducibleAt (fun z : Fin 2 → ℂ ↦ z i) 0) ∧
    Pairwise (fun i j : Fin 2 ↦ IsCoprimeAt (fun z : Fin 2 → ℂ ↦ z i)
      (fun z : Fin 2 → ℂ ↦ z j) 0) := by
  have ha : ∀ i : Fin 2, AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) i).analyticAt 0
  refine ⟨fun i ↦ ⟨ha i, gaga18_irreducibleAt_of_fderiv_ne_zero (ha i) rfl
    (gaga18_fderiv_coord_ne_zero i)⟩, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact gaga18_coordinate_coprime
  · rintro ⟨q, r, s, hq, hr, hs, hq0, h1, h0⟩
    exact gaga18_coordinate_coprime ⟨q, s, r, hq, hs, hr, hq0, h0, h1⟩
  · exact (hij rfl).elim

theorem gaga18_axis_data_aux :
    AnalyticAt ℂ gaga18_axis 0 ∧ IsIrreducibleAt gaga18_axis 0 :=
  gaga18_coordinate_data_aux.1 0

/-- Squarefreeness of a coordinate germ and its specified analytic unit multiple.
Source: Gunning--Rossi, II.B, Theorems 3--6 (units preserve irreducible elements). -/
private theorem gaga18_irreducible_germ_of_irreducibleAt
    {f : (Fin 2 → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hi : IsIrreducibleAt f 0) :
    Irreducible (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt 2 0) := by
  refine ⟨fun hu ↦ (hu.map ((Filter.Germ.valueRingHom
    (X := Fin 2 → ℂ) (E := ℂ)).comp
      (AnalyticDivisorAlgebraic11.analyticGermAtSubring 2 0).subtype)).ne_zero hi.1, ?_⟩
  intro a b hab
  obtain ⟨g, hg, hga⟩ := a.2
  obtain ⟨h, hh, hhb⟩ := b.2
  have hfac : f =ᶠ[𝓝 0] fun x ↦ g x * h x := by
    apply Filter.Germ.coe_eq.mp
    calc
      Filter.Germ.ofFun f = (a * b).1 := congrArg Subtype.val hab
      _ = a.1 * b.1 := rfl
      _ = Filter.Germ.ofFun g * Filter.Germ.ofFun h := congrArg₂ (· * ·) hga.symm hhb.symm
      _ = Filter.Germ.ofFun (fun x ↦ g x * h x) := rfl
  rcases hi.2 g h hg hh hfac with hg0 | hh0
  · left
    rw [isUnit_iff_exists_inv]
    let q : AnalyticGermAt 2 0 :=
      ⟨Filter.Germ.ofFun (fun z ↦ (g z)⁻¹), fun z ↦ (g z)⁻¹, hg.inv hg0, rfl⟩
    refine ⟨q, Subtype.ext ?_⟩
    change a.1 * q.1 = 1
    rw [← hga]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg.continuousAt.eventually_ne hg0] with z hz
    exact mul_inv_cancel₀ hz
  · right
    rw [isUnit_iff_exists_inv]
    let q : AnalyticGermAt 2 0 :=
      ⟨Filter.Germ.ofFun (fun z ↦ (h z)⁻¹), fun z ↦ (h z)⁻¹, hh.inv hh0, rfl⟩
    refine ⟨q, Subtype.ext ?_⟩
    change b.1 * q.1 = 1
    rw [← hhb]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hh.continuousAt.eventually_ne hh0] with z hz
    exact mul_inv_cancel₀ hz

theorem gaga18_reduced_unit_data_aux
    (hf : AnalyticAt ℂ gaga18_axis 0)
    (hug : AnalyticAt ℂ (fun z ↦ gaga18_unit z * gaga18_axis z) 0) :
    Squarefree (⟨Filter.Germ.ofFun gaga18_axis, gaga18_axis, hf, rfl⟩ : AnalyticGermAt 2 0) ∧
    Squarefree (⟨Filter.Germ.ofFun (fun z ↦ gaga18_unit z * gaga18_axis z),
      (fun z ↦ gaga18_unit z * gaga18_axis z), hug, rfl⟩ : AnalyticGermAt 2 0) := by
  let F : AnalyticGermAt 2 0 := ⟨Filter.Germ.ofFun gaga18_axis, gaga18_axis, hf, rfl⟩
  have hFs : Squarefree F :=
    (gaga18_irreducible_germ_of_irreducibleAt hf gaga18_axis_data_aux.2).squarefree
  have hu : AnalyticAt ℂ gaga18_unit 0 := analyticAt_const.add hf
  have hu0 : gaga18_unit 0 ≠ 0 := by simp [gaga18_unit]
  let U : AnalyticGermAt 2 0 :=
    ⟨Filter.Germ.ofFun gaga18_unit, gaga18_unit, hu, rfl⟩
  have hUu : IsUnit U := by
    rw [isUnit_iff_exists_inv]
    let V : AnalyticGermAt 2 0 :=
      ⟨Filter.Germ.ofFun (fun z ↦ (gaga18_unit z)⁻¹),
        (fun z ↦ (gaga18_unit z)⁻¹), hu.inv hu0, rfl⟩
    refine ⟨V, Subtype.ext ?_⟩
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hu.continuousAt.eventually_ne hu0] with z hz
    exact mul_inv_cancel₀ hz
  let G : AnalyticGermAt 2 0 :=
    ⟨Filter.Germ.ofFun (fun z ↦ gaga18_unit z * gaga18_axis z),
      (fun z ↦ gaga18_unit z * gaga18_axis z), hug, rfl⟩
  have hGF : Associated G F := by
    have he : G = F * U := by
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun z ↦ mul_comm _ _
    rw [he]
    exact associated_mul_unit_left F U hUu
  exact ⟨hFs, hGF.squarefree_iff.mpr hFs⟩

/-- No germ is irreducible on the zero-dimensional domain.
Source: Gunning--Rossi, II.B, Definition 1 (the zero-variable local ring is `ℂ`). -/
theorem gaga18_no_irreducible_zero (p : Fin 0 → ℂ) (g : (Fin 0 → ℂ) → ℂ) :
    ¬ IsIrreducibleAt g p := by
  intro hi
  have he : g =ᶠ[𝓝 p] fun _ ↦ (0 : ℂ) * 0 := Eventually.of_forall fun z ↦ by
    rw [Subsingleton.elim z p, zero_mul]
    exact hi.1
  rcases hi.2 (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const he with h | h
  · exact h rfl
  · exact h rfl

open Polynomial
open scoped nonZeroDivisors

private theorem gaga18_not_square_cube_fraction {R : Type*} [CommRing R] [IsDomain R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] (p : R) (hp : Irreducible p) :
    ∀ b : FractionRing R, b ^ 2 ≠ algebraMap R (FractionRing R) (p ^ 3) := by
  classical
  intro b hb
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective R b
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have hc' : algebraMap R (FractionRing R) c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne hc0
  have he : algebraMap R (FractionRing R) (a ^ 2) =
      algebraMap R (FractionRing R) (p ^ 3 * c ^ 2) := by
    field_simp at hb
    simpa only [map_pow, map_mul, mul_comm] using hb
  have he' : a ^ 2 = p ^ 3 * c ^ 2 :=
    (FaithfulSMul.algebraMap_injective R (FractionRing R)) he
  have hfac : factorization (a ^ 2) = factorization (p ^ 3 * c ^ 2) :=
    congrArg (fun x : R ↦ factorization x) he'
  have hf : factorization (a ^ 2) (normalize p) =
      factorization (p ^ 3 * c ^ 2) (normalize p) := by rw [hfac]
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [factorization_pow, factorization_mul (pow_ne_zero 3 hp0) (pow_ne_zero 2 hc0),
    factorization_pow, factorization_pow] at hf
  have hpp : factorization p (normalize p) = 1 := by
    simp [factorization, UniqueFactorizationMonoid.normalizedFactors_irreducible hp]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, hpp, mul_one] at hf
  omega

private def gaga18_coordGerm {n : ℕ} (i : Fin n) : AnalyticGerm n :=
  ⟨Filter.Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩

private theorem gaga18_coordGerm_regular_last (n : ℕ) :
    IsRegularInLast (gaga18_coordGerm (Fin.last n)) := by
  refine ⟨fun z : Fin (n + 1) → ℂ ↦ z (Fin.last n),
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
      (Fin.last n)).analyticAt 0, rfl, ?_⟩
  simp only [Pi.single_eq_same]
  change analyticOrderAt (id : ℂ → ℂ) 0 ≠ ⊤
  rw [analyticOrderAt_id]
  exact ENat.one_ne_top

private theorem gaga18_coordGerm_not_isUnit (n : ℕ) :
    ¬ IsUnit (gaga18_coordGerm (Fin.last n)) := by
  intro hu
  have hv := hu.map (analyticGermValue (n + 1))
  have hz : analyticGermValue (n + 1) (gaga18_coordGerm (Fin.last n)) = 0 := rfl
  exact not_isUnit_zero (hz ▸ hv)

private theorem gaga18_exists_weierstrassEmbedding (n : ℕ) :
    ∃ ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1),
      IsWeierstrassEmbedding ι := by
  obtain ⟨ι, P, hι, -⟩ := spec_preparation_transfer
    (gaga18_coordGerm_regular_last n) (gaga18_coordGerm_not_isUnit n)
  exact ⟨ι, hι⟩

private theorem gaga18_coordGerm_one_irreducible :
    Irreducible (gaga18_coordGerm (0 : Fin 1)) := by
  obtain ⟨ι, hι⟩ := gaga18_exists_weierstrassEmbedding 0
  letI := spec_analyticGerm_ufd 0
  letI : IsDomain (AnalyticGerm 0) := {}
  have hX : Irreducible (X : Polynomial (AnalyticGerm 0)) := irreducible_X
  have hW : IsWeierstrassPolynomial (X : Polynomial (AnalyticGerm 0)) := by
    exact ⟨monic_X, by simp [analyticGermMaximalIdeal]⟩
  have hi := (spec_irreducible_transfer ι hι hW).mp hX
  obtain ⟨h, hh, hXh⟩ := hι.2.2
  have he : h = gaga18_coordGerm (0 : Fin 1) := by
    apply Subtype.ext
    exact hh
  simpa [hXh, he] using hi

private theorem gaga18_irreducibleAt_of_analyticGerm {n : ℕ}
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0)
    (hi : Irreducible (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGerm n)) :
    IsIrreducibleAt f 0 := by
  refine ⟨?_, ?_⟩
  · by_contra hf0
    let q : AnalyticGerm n := ⟨Filter.Germ.ofFun (fun z ↦ (f z)⁻¹),
      fun z ↦ (f z)⁻¹, hf.inv hf0, rfl⟩
    apply hi.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨q, Subtype.ext ?_⟩
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hf.continuousAt.eventually_ne hf0] with x hx
    exact mul_inv_cancel₀ hx
  · intro g h hg hh hfac
    let G : AnalyticGerm n := ⟨Filter.Germ.ofFun g, g, hg, rfl⟩
    let H : AnalyticGerm n := ⟨Filter.Germ.ofFun h, h, hh, rfl⟩
    have heq : (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGerm n) = G * H := by
      apply Subtype.ext
      exact Filter.Germ.coe_eq.mpr hfac
    rcases hi.isUnit_or_isUnit heq with hG | hH
    · left
      have hv := hG.map (analyticGermValue n)
      intro hg0
      have hz : analyticGermValue n G = 0 := by change g 0 = 0; exact hg0
      exact not_isUnit_zero (hz ▸ hv)
    · right
      have hv := hH.map (analyticGermValue n)
      intro hh0
      have hz : analyticGermValue n H = 0 := by change h 0 = 0; exact hh0
      exact not_isUnit_zero (hz ▸ hv)

private theorem gaga18_cusp_analytic : AnalyticAt ℂ gaga18_cusp 0 := by
  have h0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have h1 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  exact (h1.pow 2).sub (h0.pow 3)

theorem gaga18_cusp_irreducible_aux :
    AnalyticAt ℂ gaga18_cusp 0 ∧ IsIrreducibleAt gaga18_cusp 0 := by
  refine ⟨gaga18_cusp_analytic, ?_⟩
  let z : AnalyticGerm 1 := gaga18_coordGerm (0 : Fin 1)
  let P : Polynomial (AnalyticGerm 1) := X ^ 2 - C (z ^ 3)
  letI := spec_analyticGerm_ufd 1
  letI : StrongNormalizationMonoid (AnalyticGerm 1) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : IsDomain (AnalyticGerm 1) := {}
  have hPmonic : P.Monic := monic_X_pow_sub_C _ (by decide)
  have hPirr : Irreducible P := by
    have hk : Irreducible
        (X ^ 2 - C (algebraMap (AnalyticGerm 1) (FractionRing (AnalyticGerm 1)) (z ^ 3))) :=
      X_pow_sub_C_irreducible_of_prime Nat.prime_two
        (gaga18_not_square_cube_fraction z gaga18_coordGerm_one_irreducible)
    apply (hPmonic.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (AnalyticGerm 1))).mpr
    simpa [P] using hk
  have hPW : IsWeierstrassPolynomial P := by
    have hdeg : P.natDegree = 2 := by
      change (X ^ 2 - C (z ^ 3)).natDegree = 2
      exact natDegree_X_pow_sub_C
    refine ⟨hPmonic, by omega, ?_⟩
    intro j hj
    rw [hdeg] at hj
    change analyticGermValue 1 (P.coeff j) = 0
    interval_cases j
    · change analyticGermValue 1 ((X ^ 2 - C (z ^ 3)).coeff 0) = 0
      have hc : (X ^ 2 - C (z ^ 3) : Polynomial (AnalyticGerm 1)).coeff 0 =
          -(z ^ 3) := by
        simp only [coeff_sub, coeff_X_pow, OfNat.ofNat, coeff_C_zero, zero_sub]
        norm_num
      rw [hc]
      simp only [map_neg, map_pow, neg_eq_zero]
      change (0 : ℂ) ^ 3 = 0
      norm_num
    · change analyticGermValue 1 ((X ^ 2 - C (z ^ 3)).coeff 1) = 0
      have hc : (X ^ 2 - C (z ^ 3) : Polynomial (AnalyticGerm 1)).coeff 1 = 0 := by
        simp only [coeff_sub, coeff_X_pow, OfNat.ofNat, coeff_C, sub_zero]
        norm_num
      rw [hc, map_zero]
  obtain ⟨ι, hι⟩ := gaga18_exists_weierstrassEmbedding 1
  have hPi : Irreducible (ι P) := (spec_irreducible_transfer ι hι hPW).mp hPirr
  obtain ⟨w, hw, hX⟩ := hι.2.2
  have hw' : w = gaga18_coordGerm (1 : Fin 2) := by
    apply Subtype.ext
    exact hw
  have hix : ι X = gaga18_coordGerm (1 : Fin 2) := hX.trans hw'
  obtain ⟨a, ha, haz, hCa⟩ := hι.2.1 z
  have ht : Tendsto (fun x : Fin 2 → ℂ ↦ fun i : Fin 1 ↦ x i.castSucc)
      (nhds 0) (nhds 0) := by
    have hc : Continuous (fun x : Fin 2 → ℂ ↦ fun i : Fin 1 ↦ x i.castSucc) := by
      fun_prop
    exact hc.continuousAt
  have hia : ι (C z) = gaga18_coordGerm (0 : Fin 2) := by
    apply Subtype.ext
    rw [← hCa]
    apply Filter.Germ.coe_eq.mpr
    have he : ∀ᶠ x in nhds (0 : Fin 1 → ℂ), a x = x 0 := by
      apply Filter.Germ.coe_eq.mp
      exact haz
    filter_upwards [ht.eventually he] with x hx
    simpa using hx
  have heq : ι P =
      (⟨Filter.Germ.ofFun gaga18_cusp, gaga18_cusp, gaga18_cusp_analytic, rfl⟩ :
        AnalyticGerm 2) := by
    rw [show P = X ^ 2 - C (z ^ 3) by rfl, map_sub, map_pow,
      show C (z ^ 3) = (C z) ^ 3 by rw [map_pow], map_pow, hix, hia]
    rfl
  exact gaga18_irreducibleAt_of_analyticGerm gaga18_cusp_analytic (heq ▸ hPi)

theorem gaga18_node_factorization_aux :
    ∃ s : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ s 0 ∧ s 0 = 1 ∧
      (∀ᶠ z in 𝓝 0, s z ^ 2 = 1 + z 0) ∧
      (gaga18_node =ᶠ[𝓝 0] fun z ↦ (z 1 - z 0 * s z) * (z 1 + z 0 * s z)) ∧
      IsIrreducibleAt (fun z ↦ z 1 - z 0 * s z) 0 ∧
      IsIrreducibleAt (fun z ↦ z 1 + z 0 * s z) 0 ∧
      ¬ IsIrreducibleAt gaga18_node 0 := by
  let t : (Fin 2 → ℂ) → ℂ := fun z ↦ 1 + z 0
  let s : (Fin 2 → ℂ) → ℂ := fun z ↦ Complex.exp (Complex.log (t z) / 2)
  have ht : AnalyticAt ℂ t 0 := analyticAt_const.add
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0)
  have hlog : AnalyticAt ℂ Complex.log 1 := by
    apply DifferentiableOn.analyticAt (s := Complex.slitPlane)
    · intro z hz
      exact Complex.differentiableAt_log hz |>.differentiableWithinAt
    · exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hs : AnalyticAt ℂ s 0 := by
    apply AnalyticAt.cexp'
    exact (hlog.comp_of_eq ht (by simp [t])).div_const
  have hs0 : s 0 = 1 := by simp [s, t]
  have ht_ne : ∀ᶠ z in 𝓝 0, t z ≠ 0 := ht.continuousAt.eventually_ne (by simp [t])
  have hs_sq : ∀ᶠ z in 𝓝 0, s z ^ 2 = 1 + z 0 := by
    filter_upwards [ht_ne] with z hz
    rw [show s z ^ 2 = Complex.exp (Complex.log (t z)) by
      simp only [s, pow_two, ← Complex.exp_add]
      congr 1
      ring]
    simpa only [t] using Complex.exp_log hz
  let fminus : (Fin 2 → ℂ) → ℂ := fun z ↦ z 1 - z 0 * s z
  let fplus : (Fin 2 → ℂ) → ℂ := fun z ↦ z 1 + z 0 * s z
  have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  have hminus : AnalyticAt ℂ fminus 0 := h1.sub (h0.mul hs)
  have hplus : AnalyticAt ℂ fplus 0 := h1.add (h0.mul hs)
  have hdminus : fderiv ℂ fminus 0 ≠ 0 := by
    have hd0 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 0)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0) 0 := by fun_prop
    have hd1 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) 0 := by fun_prop
    have hd : HasFDerivAt fminus _ 0 := hd1.sub (hd0.mul hs.differentiableAt.hasFDerivAt)
    intro he
    have hv := congrArg (fun L ↦ L (Pi.single 1 1)) (hd.fderiv.symm.trans he)
    simp [hs0] at hv
  have hdplus : fderiv ℂ fplus 0 ≠ 0 := by
    have hd0 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 0)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0) 0 := by fun_prop
    have hd1 : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) 0 := by fun_prop
    have hd : HasFDerivAt fplus _ 0 := hd1.add (hd0.mul hs.differentiableAt.hasFDerivAt)
    intro he
    have hv := congrArg (fun L ↦ L (Pi.single 1 1)) (hd.fderiv.symm.trans he)
    simp [hs0] at hv
  have himinus : IsIrreducibleAt fminus 0 :=
    gaga18_irreducibleAt_of_fderiv_ne_zero hminus (by simp [fminus, hs0]) hdminus
  have hiplus : IsIrreducibleAt fplus 0 :=
    gaga18_irreducibleAt_of_fderiv_ne_zero hplus (by simp [fplus, hs0]) hdplus
  have hfac : gaga18_node =ᶠ[𝓝 0] fun z ↦ fminus z * fplus z := by
    filter_upwards [hs_sq] with z hz
    simp only [gaga18_node, fminus, fplus]
    rw [← hz]
    ring
  refine ⟨s, hs, hs0, hs_sq, hfac, himinus, hiplus, ?_⟩
  intro hi
  rcases hi.2 fminus fplus hminus hplus hfac with hm | hp
  · exact hm (by simp [fminus, hs0])
  · exact hp (by simp [fplus, hs0])

theorem gaga18_concrete_data_aux :
    AnalyticAt ℂ gaga18_axis 0 ∧ IsIrreducibleAt gaga18_axis 0 ∧
    AnalyticAt ℂ gaga18_crossing 0 ∧
    AnalyticAt ℂ gaga18_cusp 0 ∧ IsIrreducibleAt gaga18_cusp 0 ∧
    AnalyticAt ℂ gaga18_node 0 ∧ ¬ IsIrreducibleAt gaga18_node 0 ∧
    AnalyticAt ℂ gaga18_unit 0 ∧ gaga18_unit 0 ≠ 0 := by
  have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  obtain ⟨s, _, _, _, _, _, _, hn⟩ := gaga18_node_factorization_aux
  exact ⟨gaga18_axis_data_aux.1, gaga18_axis_data_aux.2, h0.mul h1,
    gaga18_cusp_irreducible_aux.1, gaga18_cusp_irreducible_aux.2,
    (h1.pow 2).sub ((h0.pow 2).mul (analyticAt_const.add h0)), hn,
    analyticAt_const.add h0, by simp [gaga18_unit]⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic18
