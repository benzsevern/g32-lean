import HodgeLean.Foundations.AnalyticGermDimension

/-! # Proof obligations for anchored analytic germs and cones

HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

private def adim3_coordinate (n : ℕ) (i : Fin n) : AnalyticGerm n :=
  ⟨Filter.Germ.ofFun (fun z ↦ z i), fun z ↦ z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩

private theorem adim3_analyticGerm_isLocalRing (n : ℕ) : IsLocalRing (AnalyticGerm n) := by
  apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
  intro a b hab
  rw [analyticGerm_isUnit_iff] at hab
  simp only [map_add] at hab
  by_cases ha : analyticGermValue n a = 0
  · right
    rw [analyticGerm_isUnit_iff]
    simpa [ha] using hab
  · left
    rwa [analyticGerm_isUnit_iff]

private theorem adim3_minimalPrime_isMaximal_of_lt_one {R : Type*} [CommRing R]
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes)
    (hdim : ringKrullDim (R ⧸ P) < (1 : WithBot ℕ∞)) : P.IsMaximal := by
  letI : P.IsPrime := hP.isPrime
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr
  letI : Ring.KrullDimLE 0 (R ⧸ P) := Ring.krullDimLE_iff.mpr <|
    le_of_not_gt (fun hpos ↦ not_lt_of_ge ((WithBot.one_le_iff_pos _).mpr hpos) hdim)
  apply Ring.KrullDimLE.isField_of_isDomain

private theorem adim3_eq_minimalPrime_of_isMaximal {R : Type*} [CommRing R]
    [IsLocalRing R] (I P : Ideal R) (hI : I.radical = I)
    (hP : P ∈ I.minimalPrimes) (hPm : P.IsMaximal) : I = P := by
  have hPeq : P = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hPm
  have hunique : ∀ Q ∈ I.minimalPrimes, Q = P := by
    intro Q hQ
    have hQP : Q ≤ P := hPeq.symm ▸ IsLocalRing.le_maximalIdeal hQ.isPrime.ne_top
    exact hQP.antisymm (hP.2 hQ.1 hQP)
  rw [← hI, ← Ideal.sInf_minimalPrimes]
  apply le_antisymm (sInf_le hP)
  exact le_sInf fun Q hQ ↦ (hunique Q hQ).ge

private theorem adim3_maximalIdeal_eq_valueKernel (n : ℕ) [IsLocalRing (AnalyticGerm n)] :
    IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
  symm
  apply IsLocalRing.eq_maximalIdeal
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  refine ⟨⟨Filter.Germ.ofFun (fun _ ↦ c), fun _ ↦ c, (by fun_prop), rfl⟩, ?_⟩
  rfl
private theorem adim3_zero_mul (n : ℕ) (f g : AnalyticGerm n) :
    adim2_zero n (f * g) = adim2_zero n f ⊔ adim2_zero n g := by
  obtain ⟨ff, hff, ef⟩ := f.property
  obtain ⟨gg, hgg, eg⟩ := g.property
  unfold adim2_zero
  change (f.val * g.val).map (· = 0) =
    f.val.map (· = 0) ⊔ g.val.map (· = 0)
  rw [← ef, ← eg]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with z
  exact propext mul_eq_zero

private theorem adim3_zeroSet_inf (n : ℕ) (P Q : Ideal (AnalyticGerm n)) :
    adim2_zeroSet n (P ⊓ Q) = adim2_zeroSet n P ⊔ adim2_zeroSet n Q := by
  apply le_antisymm
  · let a := adim2_generators n P
    let b := adim2_generators n Q
    have hP : Ideal.span (a : Set (AnalyticGerm n)) = P :=
      ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P).choose_spec
    have hQ : Ideal.span (b : Set (AnalyticGerm n)) = Q :=
      ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) Q).choose_spec
    have hpair : adim2_zeroSet n (P ⊓ Q) ≤
        a.inf fun f ↦ b.inf fun g ↦ adim2_zero n f ⊔ adim2_zero n g := by
      apply Finset.le_inf
      intro f hf
      apply Finset.le_inf
      intro g hg
      rw [← adim3_zero_mul]
      have hr : adim2_zero n (f * g) =
          adim2_zeroSet n (adim2_ideal n (adim2_zero n (f * g))) := by
        simpa using (adim2_recovery n {f * g}).symm
      rw [hr]
      apply (adim2_galois n _ _).mpr
      intro x hx
      change adim2_zeroSet n (P ⊓ Q) ≤ adim2_zero n x
      change adim2_zero n (f * g) ≤ adim2_zero n x at hx
      apply le_trans ?_ hx
      apply (adim2_galois n _ _).mp le_rfl
      constructor
      · exact P.mul_mem_right g (hP ▸ Ideal.subset_span hf)
      · exact Q.mul_mem_left f (hQ ▸ Ideal.subset_span hg)
    refine hpair.trans ?_
    change a.inf (fun f ↦ b.inf fun g ↦ adim2_zero n f ⊔ adim2_zero n g) ≤
      a.inf (adim2_zero n) ⊔ b.inf (adim2_zero n)
    rw [Finset.inf_sup_distrib_right]
    simp_rw [Finset.inf_sup_distrib_left]
    exact le_rfl
  · apply sup_le
    · apply (adim2_galois n _ _).mpr
      exact inf_le_left.trans ((adim2_galois n _ _).mp le_rfl)
    · apply (adim2_galois n _ _).mpr
      exact inf_le_right.trans ((adim2_galois n _ _).mp le_rfl)

private theorem adim3_zeroSet_finset_inf (n : ℕ)
    (F : Finset (Ideal (AnalyticGerm n))) :
    adim2_zeroSet n (F.inf id) = F.sup (adim2_zeroSet n) := by
  induction F using Finset.cons_induction with
  | empty =>
      apply bot_unique
      have hmem : (1 : AnalyticGerm n) ∈
          adim2_ideal n (adim2_zeroSet n (⊤ : Ideal (AnalyticGerm n))) :=
        (adim2_galois n _ _).mp le_rfl (by simp)
      change adim2_zeroSet n (⊤ : Ideal (AnalyticGerm n)) ≤ adim2_zero n 1 at hmem
      have hone : adim2_zero n (1 : AnalyticGerm n) = ⊥ := by
        unfold adim2_zero
        apply Filter.Germ.coe_eq.mpr
        filter_upwards with z
        exact propext (by simp)
      simpa [hone] using hmem
  | cons P F hPF ih =>
      rw [Finset.inf_cons, adim3_zeroSet_inf, ih, Finset.sup_cons]
      rfl

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.A,
local equations and translation of analytic germs. -/
theorem adim3_local_equations_aux (n : ℕ) (A : Set (Fin n → ℂ))
    (hA : IsClosedAnalytic (Fin n → ℂ) A) (x : Fin n → ℂ) :
    ∃ s : Finset (AnalyticGerm n), adim2_germ n A x = s.inf (adim2_zero n) := by
  classical
  by_cases hx : x ∈ A
  · obtain ⟨U, hU, hxU, hUt, m, f, hf, hzero⟩ := hA.2 x hx
    simp only [chartAt_self_eq] at hxU hzero
    change x ∈ U at hxU
    change ∀ z ∈ U, (z ∈ A ↔ ∀ i, f i z = 0) at hzero
    let g : Fin m → AnalyticGerm n := fun i =>
      ⟨Germ.ofFun (fun z => f i (x + z)), fun z => f i (x + z),
        (hf i x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), rfl⟩
    refine ⟨Finset.univ.image g, ?_⟩
    simp only [adim2_germ, adim2_zero, Finset.inf_image, Finset.inf_apply]
    have hinf : ∀ t : Finset (Fin m),
        t.inf (adim2_zero n ∘ g) =
          Filter.Germ.ofFun (fun z => ∀ i ∈ t, f i (x + z) = 0) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          apply Filter.Germ.coe_eq.mpr
          exact Filter.Eventually.of_forall (by simp)
      | @insert a t ha ih =>
          rw [Finset.inf_insert, ih]
          apply Filter.Germ.coe_eq.mpr
          exact Filter.Eventually.of_forall (by simp [adim2_zero, g, ha])
    rw [hinf]
    apply Filter.Germ.coe_eq.mpr
    have hc : ContinuousAt (fun z : Fin n → ℂ => x + z) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds (by simpa using hxU))] with z hz
    simp only [Finset.mem_univ, forall_const, g]
    exact propext (hzero (x + z) hz)
  · refine ⟨{1}, ?_⟩
    apply Filter.Germ.coe_eq.mpr
    have hc : ContinuousAt (fun z : Fin n → ℂ => x + z) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [show {z | x + z ∉ A} ∈ 𝓝 0 by
      exact hc.preimage_mem_nhds
        ((isOpen_compl_iff.mpr hA.1).mem_nhds (by simpa using (show x ∈ Aᶜ from hx)))]
      with z hz
    simp [adim2_germ, adim2_zero, hz]

/-- Source: Gunning--Rossi, III.A, zero germs; de Jong--Pfister,
Local Analytic Geometry, Chapters 3--4, minimal primes in Noetherian local rings. -/
theorem adim3_minimal_prime_cover_aux (n : ℕ) (s : Finset (AnalyticGerm n)) :
    ∃ F : Finset (Ideal (AnalyticGerm n)),
      (F : Set (Ideal (AnalyticGerm n))) =
        (adim2_ideal n (s.inf (adim2_zero n))).minimalPrimes ∧
      s.inf (adim2_zero n) = F.sup (adim2_zeroSet n) := by
  let I := adim2_ideal n (s.inf (adim2_zero n))
  letI : IsNoetherianRing (AnalyticGerm n) := adim_noetherian n
  let hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (AnalyticGerm n) I
  let F := hfin.toFinset
  refine ⟨F, hfin.coe_toFinset, ?_⟩
  rw [← adim2_recovery n s, ← adim3_zeroSet_finset_inf]
  congr 1
  rw [Finset.inf_id_eq_sInf, hfin.coe_toFinset, Ideal.sInf_minimalPrimes,
    adim2_radical]

/-- Source: Chirka, Complex Analytic Sets, §§2--3, local dimension;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, the cone route. -/
theorem adim3_cone_lower_bound_aux (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A)
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    ∀ x ∈ A, ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) := by
  intro x hx P hP
  apply le_of_not_gt
  intro hdim
  let S := adim2_germ (n + 1) A x
  let I := adim2_ideal (n + 1) S
  letI := adim3_analyticGerm_isLocalRing (n + 1)
  have hPm : P.IsMaximal := adim3_minimalPrime_isMaximal_of_lt_one I P hP hdim
  have hIP : I = P :=
    adim3_eq_minimalPrime_of_isMaximal I P (adim2_radical (n + 1) S) hP hPm
  have hPval : P = analyticGermMaximalIdeal (n + 1) := by
    rw [← adim3_maximalIdeal_eq_valueKernel]
    exact IsLocalRing.eq_maximalIdeal hPm
  have hcoord (i : Fin (n + 1)) : S ≤ adim2_zero (n + 1) (adim3_coordinate (n + 1) i) := by
    change adim3_coordinate (n + 1) i ∈ I
    rw [hIP, hPval]
    rfl
  have hcoord' (i : Fin (n + 1)) :
      ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), x + z ∈ A → z i = 0 := by
    have hi := hcoord i
    change (fun z ↦ x + z ∈ A) ≤ᶠ[𝓝 0] (fun z ↦ z i = 0) at hi
    filter_upwards [hi] with z hz
    exact hz
  have hall : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), x + z ∈ A → z = 0 := by
    filter_upwards [eventually_all.mpr hcoord'] with z hz hzx
    funext i
    exact hz i hzx
  have hcont : ContinuousAt (fun t : ℂ ↦ (t - 1) • x) 1 := by fun_prop
  have horbit : ∀ᶠ t in 𝓝 (1 : ℂ), (t - 1) • x = 0 := by
    have hall' : ∀ᶠ z in 𝓝 ((fun t : ℂ ↦ (t - 1) • x) 1), x + z ∈ A → z = 0 := by
      simpa using hall
    filter_upwards [hcont.eventually hall', eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)]
      with t ht ht0
    apply ht
    simpa [sub_smul] using hscale t ht0 x hx
  have hx0 : x ≠ 0 := fun h ↦ hzero (h ▸ hx)
  have hone : ∀ᶠ t in 𝓝 (1 : ℂ), t = 1 := by
    filter_upwards [horbit] with t ht
    have ht' : t - (1 : ℂ) = 0 := (smul_eq_zero.mp ht).resolve_right hx0
    exact sub_eq_zero.mp ht'
  have hopen : IsOpen ({1} : Set ℂ) := by
    rw [isOpen_iff_mem_nhds]
    rintro y rfl
    change {t : ℂ | t = 1} ∈ 𝓝 (1 : ℂ) at hone
    simpa only [Set.setOf_eq_eq_singleton] using hone
  exact (not_isOpen_singleton (1 : ℂ)) hopen

end HodgeLean.Foundations
