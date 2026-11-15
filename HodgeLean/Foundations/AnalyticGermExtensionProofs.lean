import HodgeLean.Foundations.AnalyticGermNormalization
import HodgeLean.Foundations.AnalyticGermCone
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Analytic extension preparation

Implication from finite local parameter maps to representative coordinate equations,
and from bounded punctured holomorphy to extension at a point; parameter calibration.
Image surjectivity, component comparison and point Remmert–Stein remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

private theorem adim6_prime_coheight_eq_quotient (n : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime) :
    (Order.coheight (⟨P, hP⟩ : PrimeSpectrum (AnalyticGerm n)) : WithBot ℕ∞) =
      ringKrullDim (AnalyticGerm n ⧸ P) := by
  rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
  apply Order.krullDim_eq_of_orderIso
  let e : Set.Ici (⟨P, hP⟩ : PrimeSpectrum (AnalyticGerm n)) ≃
      PrimeSpectrum.zeroLocus (P : Set (AnalyticGerm n)) :=
    Set.equivOfEq (by
      ext Q
      simp only [Set.mem_Ici, PrimeSpectrum.mem_zeroLocus]
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).symm)
  exact { e with map_rel_iff' := by intro a b; rfl }

private def adim6_drop (n : ℕ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc

private def adim6_include (n : ℕ) : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ if h : (i : ℕ) < n then
    ContinuousLinearMap.proj (⟨i, h⟩ : Fin n) else 0

private theorem adim6_include_tendsto (n : ℕ) :
    Tendsto (adim6_include n) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (adim6_include n) (𝓝 0) (𝓝 (adim6_include n 0)) :=
    (adim6_include n).continuous.continuousAt
  rw [map_zero] at h
  exact h

private def adim6_restrict (n : ℕ) : AnalyticGerm (n + 1) →+* AnalyticGerm n where
  toFun g := ⟨g.1.compTendsto (adim6_include n) (adim6_include_tendsto n), by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨f ∘ adim6_include n,
      hf.comp_of_eq ((adim6_include n).analyticAt 0) (map_zero _), ?_⟩
    exact congrArg (fun q ↦ q.compTendsto (adim6_include n)
      (adim6_include_tendsto n)) hfg⟩
  map_one' := rfl
  map_mul' g h := by
    let hi := adim6_include_tendsto n
    apply Subtype.ext
    change (g.1 * h.1).compTendsto (adim6_include n) hi =
      g.1.compTendsto (adim6_include n) hi * h.1.compTendsto (adim6_include n) hi
    exact Filter.Germ.inductionOn g.1 fun _ ↦ Filter.Germ.inductionOn h.1 fun _ ↦ rfl
  map_zero' := rfl
  map_add' g h := by
    let hi := adim6_include_tendsto n
    apply Subtype.ext
    change (g.1 + h.1).compTendsto (adim6_include n) hi =
      g.1.compTendsto (adim6_include n) hi + h.1.compTendsto (adim6_include n) hi
    exact Filter.Germ.inductionOn g.1 fun _ ↦ Filter.Germ.inductionOn h.1 fun _ ↦ rfl

private theorem adim6_restrict_surjective (n : ℕ) :
    Function.Surjective (adim6_restrict n) := by
  rintro ⟨g, f, hf, rfl⟩
  let F : (Fin (n + 1) → ℂ) → ℂ := f ∘ adim6_drop n
  have hF : AnalyticAt ℂ F 0 :=
    hf.comp_of_eq ((adim6_drop n).analyticAt 0) (map_zero _)
  refine ⟨⟨Germ.ofFun F, ⟨F, hF, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (Germ.ofFun F).compTendsto (adim6_include n) (adim6_include_tendsto n) =
    Germ.ofFun f
  change Germ.ofFun (F ∘ adim6_include n) = Germ.ofFun f
  rw [Filter.Germ.coe_eq]
  filter_upwards [] with z
  change f (adim6_drop n (adim6_include n z)) = f z
  congr 1
  funext i
  simp [adim6_drop, adim6_include]

private theorem adim6_zero_dimension :
    ringKrullDim (AnalyticGerm 0) = (0 : WithBot ℕ∞) := by
  let e : AnalyticGerm 0 ≃+* ℂ := RingEquiv.ofBijective (analyticGermValue 0) ⟨by
    rintro ⟨g, f, hf, rfl⟩ ⟨h, k, hk, rfl⟩ hv
    apply Subtype.ext
    rw [Filter.Germ.coe_eq]
    filter_upwards [] with z
    have hz : z = 0 := Subsingleton.elim _ _
    change f 0 = k 0 at hv
    simpa [hz] using hv
  , by
    intro c
    refine ⟨⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c),
      ⟨fun _ ↦ c, analyticAt_const, rfl⟩⟩, ?_⟩
    change (@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c)).value = c
    simpa using (Filter.Germ.value_ofFun (fun _ : Fin 0 → ℂ ↦ c) (0 : Fin 0 → ℂ))⟩
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field]
private theorem bounded_point_extension_one_variable (U : Set ℂ)
    (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hbounded : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    AnalyticOnNhd ℂ (Function.update f 0 (limUnder (nhdsWithin 0 {0}ᶜ) f)) U := by
  have hnhds : U ∈ nhds (0 : ℂ) := hU.mem_nhds hU0
  have hdiff : DifferentiableOn ℂ f (U \ {0}) := hf.differentiableOn
  have hbdd : BddAbove (norm ∘ f '' (U \ {0})) := by
    rcases hbounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz
  exact (Complex.differentiableOn_update_limUnder_of_bddAbove hnhds hdiff hbdd).analyticOnNhd hU

private theorem weighted_hasFDerivAt_zero {n : ℕ}
    (U : Set ((Fin n → ℂ) × ℂ)) (hU : U ∈ 𝓝 0)
    (f : ((Fin n → ℂ) × ℂ) → ℂ)
    (hb : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    HasFDerivAt (fun z => z.2 ^ 2 * f z) (0 : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ) 0 := by
  obtain ⟨C, hC⟩ := hb
  rw [hasFDerivAt_iff_isLittleO]
  simp only [zero_apply, sub_zero]
  simp only [show (0 : (Fin n → ℂ) × ℂ).2 = 0 from rfl,
    zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he : ∀ᶠ z : (Fin n → ℂ) × ℂ in 𝓝 0, ‖z‖ < ε / (|C| + 1) :=
    (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using (div_pos hε (by positivity : 0 < |C| + 1))))
  filter_upwards [hU, he] with z hz hze
  by_cases hz0 : z = 0
  · simp [hz0]
  have hbound := hC z ⟨hz, hz0⟩
  have hs : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  rw [norm_mul, norm_pow]
  calc
    ‖z.2‖ ^ 2 * ‖f z‖ ≤ ‖z‖ ^ 2 * (|C| + 1) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hs 2)
        (hbound.trans (by linarith [le_abs_self C])) (norm_nonneg _) (sq_nonneg _)
    _ ≤ ε * ‖z‖ := by
      have := (lt_div_iff₀ (by positivity : 0 < |C| + 1)).mp hze
      nlinarith [norm_nonneg z]

private theorem analytic_divide_last {n : ℕ}
    {g : (Fin n → ℂ) × ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hz : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), g (z, 0) = 0) :
    ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      g =ᶠ[𝓝 0] fun p => q p * p.2 := by
  obtain ⟨q, hq, b, _, he⟩ := AnalyticDivisorAlgebraic4.spec_weierstrass_division
    (d := 1) (a := fun _ _ => 0) hg (fun _ => analyticAt_const) (fun _ => rfl)
  simp only [AnalyticDivisorAlgebraic4.monicInLast, Fin.sum_univ_one,
    Fin.val_zero, pow_zero, pow_one, zero_mul, add_zero, mul_one] at he
  have ht : Tendsto (fun z : Fin n → ℂ => (z, (0 : ℂ))) (𝓝 0) (𝓝 0) :=
    continuousAt_id.prodMk continuousAt_const
  have hb : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), b 0 z = 0 := by
    filter_upwards [he.comp_tendsto ht, hz] with z he hz
    simpa [hz] using he.symm
  refine ⟨q, hq, ?_⟩
  filter_upwards [he, continuousAt_fst.eventually hb] with p he hb
  simpa [hb] using he

private theorem analytic_divide_last_sq {n : ℕ}
    {g : (Fin n → ℂ) × ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hz : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), g (z, 0) = 0)
    (hd : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), HasDerivAt (fun w => g (z, w)) 0 0) :
    ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      g =ᶠ[𝓝 0] fun p => q p * p.2 ^ 2 := by
  obtain ⟨q, hq, he⟩ := analytic_divide_last hg hz
  have ht : Tendsto (fun z : Fin n → ℂ => (z, (0 : ℂ))) (𝓝 0) (𝓝 0) :=
    continuousAt_id.prodMk continuousAt_const
  have hqz : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), q (z, 0) = 0 := by
    filter_upwards [hd, ht.eventually hq.eventually_analyticAt,
      ht.eventually he.eventually_nhds] with z hd hq he
    have hslice : DifferentiableAt ℂ (fun w => q (z, w)) 0 :=
      hq.differentiableAt.comp 0 (by fun_prop)
    have he' : (fun w => g (z, w)) =ᶠ[𝓝 0] (fun w => q (z, w) * w) :=
      (continuousAt_const.prodMk continuousAt_id).eventually he
    have hright := hslice.hasDerivAt.mul (hasDerivAt_id (0 : ℂ))
    have hleft := hd.congr_of_eventuallyEq he'.symm
    simpa using (hright.unique hleft)
  obtain ⟨r, hr, hqr⟩ := analytic_divide_last hq hqz
  refine ⟨r, hr, ?_⟩
  filter_upwards [he, hqr] with p he hqr
  rw [he, hqr]
  ring

private theorem weighted_analytic {n : ℕ}
    (U : Set ((Fin n → ℂ) × ℂ)) (hU : IsOpen U) (hU0 : (0 : (Fin n → ℂ) × ℂ) ∈ U)
    (f : ((Fin n → ℂ) × ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hb : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    AnalyticAt ℂ (fun z => z.2 ^ 2 * f z) 0 ∧
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), HasDerivAt (fun w => w ^ 2 * f (z, w)) 0 0 := by
  have hd0 := weighted_hasFDerivAt_zero U (hU.mem_nhds hU0) f hb
  constructor
  · apply AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn hU _ 0 hU0
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      exact hd0.differentiableAt.differentiableWithinAt
    · exact ((differentiableAt_snd.pow 2).mul
        (hf z ⟨hz, hz0⟩).differentiableAt).differentiableWithinAt
  · have ht : Tendsto (fun z : Fin n → ℂ => (z, (0 : ℂ))) (𝓝 0) (𝓝 0) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually (hU.mem_nhds hU0)] with z hz
    by_cases hz0 : z = 0
    · subst z
      simpa [Function.comp_def] using hd0.comp_hasDerivAt 0
        ((hasDerivAt_const (0 : ℂ) (0 : Fin n → ℂ)).prodMk (hasDerivAt_id 0))
    · have hne : (z, (0 : ℂ)) ≠ 0 := fun h => hz0 (congrArg Prod.fst h)
      have hfs : DifferentiableAt ℂ (fun w => f (z, w)) 0 :=
        (hf (z, 0) ⟨hz, hne⟩).differentiableAt.comp 0 (by fun_prop)
      simpa using! ((hasDerivAt_id (0 : ℂ)).pow 2).mul hfs.hasDerivAt

private theorem eq_of_eq_off_last {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (he : ∀ᶠ z in 𝓝 p, z.2 ≠ 0 → f z = g z) : f p = g p := by
  by_cases hp : p.2 = 0
  · rcases p with ⟨z, w⟩
    dsimp at hp
    subst w
    have ht : Tendsto (fun w : ℂ => (z, w)) (𝓝[≠] 0) (𝓝 (z, 0)) :=
      (continuousAt_const.prodMk continuousAt_id).mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.comp ht) (hg.tendsto.comp ht)
    filter_upwards [ht.eventually he, self_mem_nhdsWithin] with w hw hne
    exact hw hne
  · exact he.self_of_nhds hp

private theorem bounded_local_extension_product {n : ℕ}
    (U : Set ((Fin n → ℂ) × ℂ)) (hU : IsOpen U) (hU0 : (0 : (Fin n → ℂ) × ℂ) ∈ U)
    (f : ((Fin n → ℂ) × ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hb : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧ f =ᶠ[𝓝[≠] 0] q := by
  obtain ⟨hg, hd⟩ := weighted_analytic U hU hU0 f hf hb
  obtain ⟨q, hq, he⟩ := analytic_divide_last_sq hg (Eventually.of_forall (by simp)) hd
  have heq : ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), p.2 ≠ 0 → f p = q p := by
    filter_upwards [he] with p hp hne
    exact (mul_left_cancel₀ (pow_ne_zero 2 hne)) (hp.trans (mul_comm _ _))
  refine ⟨q, hq, ?_⟩
  filter_upwards [heq.eventually_nhds.filter_mono nhdsWithin_le_nhds,
    hq.eventually_continuousAt.filter_mono nhdsWithin_le_nhds,
    nhdsWithin_le_nhds (hU.mem_nhds hU0), self_mem_nhdsWithin] with p he hq hp hp0
  exact eq_of_eq_off_last (hf p ⟨hp, hp0⟩).continuousAt hq he

private def extensionSplit (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ℂ)).symm.trans
        (Equiv.prodComm _ _)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem bounded_local_extension {d : ℕ}
    (U : Set (Fin (d + 1) → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin (d + 1) → ℂ) ∈ U)
    (f : (Fin (d + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hb : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    ∃ q : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ q 0 ∧ f =ᶠ[𝓝[≠] 0] q := by
  let e := extensionSplit d
  have hV : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hV0 : (0 : (Fin d → ℂ) × ℂ) ∈ e.symm ⁻¹' U := by simpa using hU0
  have hF : AnalyticOnNhd ℂ (fun p => f (e.symm p)) ((e.symm ⁻¹' U) \ {0}) := by
    intro p hp
    have hp0 : e.symm p ≠ 0 := by simpa using hp.2
    exact (hf _ ⟨hp.1, hp0⟩).comp (e.symm.analyticAt p)
  have hB : ∃ C : ℝ, ∀ p ∈ (e.symm ⁻¹' U) \ {0}, ‖f (e.symm p)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨C, fun p hp => hC _ ⟨hp.1, ?_⟩⟩
    simpa using hp.2
  obtain ⟨q, hq, he⟩ := bounded_local_extension_product _ hV hV0 _ hF hB
  refine ⟨fun z => q (e z), ?_, ?_⟩
  · exact (by simpa using hq : AnalyticAt ℂ q (e 0)).comp (e.analyticAt 0)
  · have he' := eventually_nhdsWithin_iff.mp he
    have ht : Tendsto e (𝓝 0) (𝓝 0) := by simpa using (e.continuous.continuousAt (x := 0)).tendsto
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [ht.eventually he'] with z hz hz0
    simpa using hz (by simpa using hz0)

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.C, dimension of the convergent power series ring. -/
theorem adim6_parameter_dimension_aux (n : ℕ) :
    ringKrullDim (AnalyticGerm n) = (n : WithBot ℕ∞) := by
  induction n with
  | zero => exact adim6_zero_dimension
  | succ n ih =>
      apply le_antisymm
      · let p0 : PrimeSpectrum (AnalyticGerm (n + 1)) := ⟨⊥, inferInstance⟩
        have hp0 : (Order.coheight p0 : WithBot ℕ∞) =
            ringKrullDim (AnalyticGerm (n + 1)) := by
          rw [adim6_prime_coheight_eq_quotient (n + 1) ⊥ (inferInstance : (⊥ :
            Ideal (AnalyticGerm (n + 1))).IsPrime)]
          exact (RingEquiv.quotientBot (AnalyticGerm (n + 1))).ringKrullDim
        rw [← hp0]
        apply WithBot.coe_le_coe.mpr
        rw [Order.coheight_le_coe_iff]
        intro P hP
        have hP0 : P.asIdeal ≠ ⊥ := by
          intro h
          apply hP.ne
          apply PrimeSpectrum.ext
          exact h.symm
        obtain ⟨L, e, ι, W, hrep, hι, hW, hmem, hprime, hfinite, hinj, hdim⟩ :=
          adim5_prime_step n P.asIdeal P.isPrime hP0
        have hq : ringKrullDim
            (AnalyticGerm n ⧸ ((P.asIdeal.map e.toRingHom).comap (ι.comp C))) ≤ n := by
          rw [← ih]
          exact ringKrullDim_quotient_le _
        have hc : (Order.coheight P : WithBot ℕ∞) ≤ n := by
          rw [adim6_prime_coheight_eq_quotient (n + 1) P.asIdeal P.isPrime, ← hdim]
          exact hq
        exact (WithBot.coe_le_coe.mp hc).trans_lt
          (ENat.coe_lt_coe.mpr (Nat.lt_succ_self n))
      · have hne : adim_coordinate n ≠ 0 := by
          intro h
          have he : (fun z : Fin (n + 1) → ℂ ↦ z (Fin.last n)) =ᶠ[nhds 0] fun _ ↦ 0 :=
            Germ.coe_eq.mp (congrArg Subtype.val h)
          have hd := he.fderiv_eq (𝕜 := ℂ)
          have hv := congrArg (fun f : (Fin (n + 1) → ℂ) →L[ℂ] ℂ ↦ f (fun _ ↦ 1)) hd
          rw [fderiv_apply (𝕜 := ℂ) differentiableAt_id, fderiv_fun_id] at hv
          simp at hv
        have hz : adim6_restrict n (adim_coordinate n) = 0 := by
          apply Subtype.ext
          change (Germ.ofFun (fun z : Fin (n + 1) → ℂ ↦ z (Fin.last n))).compTendsto
            (adim6_include n) (adim6_include_tendsto n) = 0
          change Germ.ofFun ((fun z : Fin (n + 1) → ℂ ↦ z (Fin.last n)) ∘
            adim6_include n) = Germ.ofFun (fun _ : Fin n → ℂ ↦ 0)
          rw [Filter.Germ.coe_eq]
          filter_upwards [] with z
          simp [adim6_include]
        have hlower := ringKrullDim_succ_le_of_surjective (adim6_restrict n)
          (adim6_restrict_surjective n) (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hz
        simpa [ih, Nat.cast_add, Nat.cast_one] using hlower

private theorem adim6_map_preserves_germ_value (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
  letI : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro x y hxy
    rw [analyticGerm_isUnit_iff] at hxy
    simp only [map_add] at hxy
    by_cases hx : analyticGermValue n x = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [hx] using hxy
    · left
      rwa [analyticGerm_isUnit_iff]
  have hmax : IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
    symm
    apply IsLocalRing.eq_maximalIdeal
    apply RingHom.ker_isMaximal_of_surjective
    intro z
    refine ⟨⟨Germ.ofFun (fun _ ↦ z), fun _ ↦ z, analyticAt_const, rfl⟩, ?_⟩
    rfl
  intro a b hab
  obtain ⟨fa, hfa, hfarep⟩ := a.property
  let c : AnalyticGerm n :=
    ⟨Germ.ofFun (fun z ↦ fa (π z)), fun z ↦ fa (π z),
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hac : θ a = Ideal.Quotient.mk P c := hcomp a fa hfa hfarep c rfl
  have hbc : b - c ∈ P :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem b c).mp (hab.symm.trans hac)
  have hbc' : b - c ∈ analyticGermMaximalIdeal n := by
    rw [← hmax]
    exact IsLocalRing.le_maximalIdeal hP hbc
  have hval : analyticGermValue n b = analyticGermValue n c := by
    have := hbc'
    change analyticGermValue n (b - c) = 0 at this
    exact sub_eq_zero.mp (by simpa using this)
  rw [hval]
  change a.val.value = c.val.value
  rw [← hfarep]
  change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
  simp only [Germ.value_ofFun, map_zero]

set_option maxHeartbeats 400000 in
/-- Source: Grauert--Remmert, Coherent Analytic Sheaves, Chapter 5, representatives of finite local analytic algebras; Gunning--Rossi, III.C. -/
theorem adim6_representative_equations_aux (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (k : Fin n → ℕ) (a : (j : Fin n) → Fin (k j) → (Fin d → ℂ) → ℂ)
      (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      (∀ j, 0 < k j) ∧ (∀ j i, AnalyticOnNhd ℂ (a j i) V) ∧
      (∀ j i, a j i 0 = 0) ∧ IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧ π '' W ⊆ V ∧
      ∀ z ∈ W, (∀ l, f l z = 0) → ∀ j,
        z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ) = 0 := by
  classical
  let x : Fin n → AnalyticGerm n := fun j ↦
    ⟨Germ.ofFun (fun z ↦ z j), fun z ↦ z j,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) j).analyticAt 0, rfl⟩
  have hx0 (j : Fin n) : analyticGermValue n (x j) = 0 := rfl
  have hlocal := adim6_map_preserves_germ_value n d P hP π θ hcomp
  choose Q hQ hQroot using fun j ↦
    adim5_distinguished_relation n d P hP θ hfinite hlocal (x j) (hx0 j)
  let k : Fin n → ℕ := fun j ↦ (Q j).natDegree
  have hk : ∀ j, 0 < k j := fun j ↦ (hQ j).2.1
  choose a ha hga using fun (j : Fin n) (i : Fin (k j)) ↦ (Q j).coeff i |>.property
  have ha0 : ∀ j i, a j i 0 = 0 := by
    intro j i
    have hc := (hQ j).2.2 i (by simpa [k] using i.isLt)
    change analyticGermValue d ((Q j).coeff i) = 0 at hc
    change ((Q j).coeff i).val.value = 0 at hc
    rw [← hga j i] at hc
    simpa only [Germ.value_ofFun] using hc
  let ca : (j : Fin n) → Fin (k j) → AnalyticGerm n := fun j i ↦
    ⟨Germ.ofFun (fun z ↦ a j i (π z)), fun z ↦ a j i (π z),
      (ha j i).comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hca (j : Fin n) (i : Fin (k j)) :
      θ ((Q j).coeff i) = Ideal.Quotient.mk P (ca j i) :=
    hcomp ((Q j).coeff i) (a j i) (ha j i) (hga j i) (ca j i) rfl
  let r : Fin n → AnalyticGerm n := fun j ↦
    x j ^ k j + ∑ i : Fin (k j), ca j i * x j ^ (i : ℕ)
  have hrP : ∀ j, r j ∈ P := by
    intro j
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    have hlead : (Q j).coeff (k j) = 1 := by
      simpa [k] using (hQ j).1.coeff_natDegree
    have hroot := hQroot j
    rw [Polynomial.eval₂_eq_sum_range, show (Q j).natDegree + 1 = k j + 1 by rfl,
      Finset.sum_range_succ] at hroot
    rw [hlead, map_one, one_mul,
      ← Fin.sum_univ_eq_sum_range
        (fun i ↦ θ ((Q j).coeff i) * Ideal.Quotient.mk P (x j) ^ i) (k j)] at hroot
    rw [map_add, map_sum]
    simpa only [map_pow, map_mul, hca, add_comm] using hroot
  have hrspan : ∀ j, r j ∈ Ideal.span (Set.range g) := by
    intro j
    rw [hgen]
    exact hrP j
  choose c hc using fun j ↦ (Ideal.mem_span_range_iff_exists_fun.mp (hrspan j))
  choose b hb hgb using fun (j : Fin n) (l : Fin m) ↦ (c j l).property
  have hrevent : ∀ j, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ) =
        ∑ l : Fin m, b j l z * f l z := by
    intro j
    apply Filter.Germ.coe_eq.mp
    calc
      Germ.ofFun (fun z : Fin n → ℂ ↦
          z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ)) =
          (r j).val := by
        change Germ.ofFun (fun z : Fin n → ℂ ↦
          z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ)) =
          (analyticGermSubring n).subtype (r j)
        rw [show r j = x j ^ k j + ∑ i : Fin (k j), ca j i * x j ^ (i : ℕ) by rfl,
          map_add, map_pow, map_sum]
        simp only [map_mul]
        change Germ.ofFun (fun z : Fin n → ℂ ↦
          z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ)) =
          Germ.ofFun (fun z ↦ z j) ^ k j +
            ∑ i : Fin (k j), Germ.ofFun (fun z ↦ a j i (π z)) *
              Germ.ofFun (fun z ↦ z j) ^ (i : ℕ)
        change Filter.Germ.coeRingHom (𝓝 0) (fun z : Fin n → ℂ ↦
          z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ)) =
          Filter.Germ.coeRingHom (𝓝 0) (fun z : Fin n → ℂ ↦ z j) ^ k j +
            ∑ i : Fin (k j),
              Filter.Germ.coeRingHom (𝓝 0) (fun z : Fin n → ℂ ↦ a j i (π z)) *
                Filter.Germ.coeRingHom (𝓝 0) (fun z : Fin n → ℂ ↦ z j) ^ (i : ℕ)
        simp only [← map_pow, ← map_mul, ← map_sum, ← map_add]
        congr 1
        funext z
        simp only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply]
      _ = (∑ l : Fin m, c j l * g l).val := congrArg Subtype.val (hc j).symm
      _ = Germ.ofFun (fun z ↦ ∑ l : Fin m, b j l z * f l z) := by
        change (analyticGermSubring n).subtype (∑ l : Fin m, c j l * g l) = _
        rw [map_sum]
        simp only [map_mul]
        have hcval (l : Fin m) :
            (analyticGermSubring n).subtype (c j l) = Germ.ofFun (b j l) := (hgb j l).symm
        have hgval (l : Fin m) :
            (analyticGermSubring n).subtype (g l) = Germ.ofFun (f l) := (hrep l).symm
        simp_rw [hcval, hgval]
        change (∑ l : Fin m,
          Filter.Germ.coeRingHom (𝓝 0) (b j l) * Filter.Germ.coeRingHom (𝓝 0) (f l)) =
          Filter.Germ.coeRingHom (𝓝 0) (fun z ↦ ∑ l : Fin m, b j l z * f l z)
        simp only [← map_mul, ← map_sum]
        congr 1
        funext z
        simp only [Finset.sum_apply, Pi.mul_apply]
  have hanevent : ∀ᶠ y in 𝓝 (0 : Fin d → ℂ), ∀ j i, AnalyticAt ℂ (a j i) y := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro i
    exact (ha j i).eventually_analyticAt
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hanevent
  have hVanalytic : ∀ j i, AnalyticOnNhd ℂ (a j i) V := by
    intro j i y hy
    exact hVsub hy j i
  have hreqevent : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j,
      z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ) =
        ∑ l : Fin m, b j l z * f l z := by
    rw [Filter.eventually_all]
    exact hrevent
  have hpre : π ⁻¹' V ∈ 𝓝 (0 : Fin n → ℂ) := by
    apply (π.continuous.tendsto 0)
    simpa only [map_zero] using hVopen.mem_nhds hV0
  have hcommon : U ∩ π ⁻¹' V ∩ {z | ∀ j,
      z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ) =
        ∑ l : Fin m, b j l z * f l z} ∈ 𝓝 (0 : Fin n → ℂ) :=
    Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hU0) hpre) hreqevent
  obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.mp hcommon
  refine ⟨k, a, W, V, hk, hVanalytic, ha0, hWopen, hW0, ?_, hVopen, hV0, ?_, ?_⟩
  · intro z hz
    exact (hWsub hz).1.1
  · rintro _ ⟨z, hz, rfl⟩
    exact (hWsub hz).1.2
  · intro z hz hzero j
    rw [(hWsub hz).2 j]
    exact Finset.sum_eq_zero fun l _ ↦ by rw [hzero l, mul_zero]

private theorem adim6_isLocalRing (n : ℕ) : IsLocalRing (AnalyticGerm n) := by
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

private theorem adim6_maximalIdeal_eq (n : ℕ) [IsLocalRing (AnalyticGerm n)] :
    IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
  symm
  apply IsLocalRing.eq_maximalIdeal
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  refine ⟨⟨Filter.Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, ?_⟩
  rfl

/-- Source: Gunning--Rossi, III.C, finite representatives and root confinement; Chirka, Complex Analytic Sets, §3. -/
theorem adim6_confined_projection_aux (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∃ p : {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0} → V,
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧
        ∀ z, (p z).val = 0 → z.val = 0 := by
  classical
  letI := adim6_isLocalRing n
  obtain ⟨k, a, W₀, V₀, hk, ha, ha0, hW₀, hW₀0, hW₀U, hV₀, hV₀0,
      hπW₀, heq⟩ := adim6_representative_equations_aux n d m P hP π θ hfinite hcomp
        g hgen f U hU hU0 hf hrep
  let U₀ : Set ((Fin d → ℂ) × (Fin n → ℂ)) := V₀ ×ˢ W₀
  let S : Set ((Fin d → ℂ) × (Fin n → ℂ)) :=
    {y | y.1 = π y.2 ∧ ∀ l, f l y.2 = 0}
  have hU₀ : IsOpen U₀ := hV₀.prod hW₀
  have hU₀0 : (0 : (Fin d → ℂ) × (Fin n → ℂ)) ∈ U₀ := by
    exact ⟨hV₀0, hW₀0⟩
  have hf0 : ∀ l, f l 0 = 0 := by
    intro l
    have hgP : g l ∈ P := by
      rw [← hgen]
      exact Ideal.subset_span (Set.mem_range_self l)
    have hm : g l ∈ analyticGermMaximalIdeal n := by
      rw [← adim6_maximalIdeal_eq n]
      exact IsLocalRing.le_maximalIdeal hP hgP
    change (g l).val.value = 0 at hm
    rw [← hrep l] at hm
    simpa using hm
  have hS0 : (0 : (Fin d → ℂ) × (Fin n → ℂ)) ∈ S := by
    exact ⟨by simp, hf0⟩
  have hS : IsClosed {z : U₀ | z.val ∈ S} := by
    have hπc : Continuous (fun z : U₀ ↦ π z.val.2) :=
      π.continuous.comp (continuous_snd.comp continuous_subtype_val)
    have hfstc : Continuous (fun z : U₀ ↦ z.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have hfc (l : Fin m) : Continuous (fun z : U₀ ↦ f l z.val.2) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hf l z.val.2 (hW₀U z.property.2)).continuousAt.comp_of_eq
        ((continuous_snd.comp continuous_subtype_val).continuousAt) rfl
    dsimp [S]
    rw [show {z : U₀ | z.val.1 = π z.val.2 ∧ ∀ l, f l z.val.2 = 0} =
        {z : U₀ | z.val.1 = π z.val.2} ∩
          ⋂ l, {z : U₀ | f l z.val.2 = 0} by ext z; simp]
    exact (isClosed_eq hfstc hπc).inter
      (isClosed_iInter fun l ↦ isClosed_eq (hfc l) continuous_const)
  have heq' : ∀ z ∈ U₀ ∩ S, ∀ j,
      z.2 j ^ k j + ∑ i : Fin (k j), a j i z.1 * z.2 j ^ (i : ℕ) = 0 := by
    intro z hz j
    rw [hz.2.1]
    exact heq z.2 hz.1.2 hz.2.2 j
  obtain ⟨V, T, hV, hV0, hT, hT0, hTU, p₀, hp₀, hproper, hfinite₀, hzero⟩ :=
    adim5_closed_projection d n k hk a
      (fun j i ↦ ha j i 0 hV₀0) ha0 U₀ S hU₀ hU₀0 hS hS0 heq'
  let W : Set (Fin n → ℂ) := {z | (π z, z) ∈ T}
  have hW : IsOpen W := hT.preimage (π.continuous.prodMk continuous_id)
  have hW0 : (0 : Fin n → ℂ) ∈ W := by
    change (π 0, 0) ∈ T
    convert hT0 using 1 <;> simp
  have hWU : W ⊆ U := by
    intro z hz
    exact hW₀U (hTU hz).2
  let A := {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0}
  let B := {z : (Fin d → ℂ) × (Fin n → ℂ) // z ∈ T ∩ S}
  let e : A ≃ₜ B :=
    { toFun := fun z ↦ ⟨(π z.val, z.val), z.property.1, rfl, z.property.2⟩
      invFun := fun z ↦ ⟨z.val.2, by
        refine ⟨?_, z.property.2.2⟩
        change (π z.val.2, z.val.2) ∈ T
        rw [← z.property.2.1]
        exact z.property.1⟩
      left_inv := by intro z; rfl
      right_inv := by
        intro z
        apply Subtype.ext
        exact Prod.ext z.property.2.1.symm rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (π.continuous.comp continuous_subtype_val).prodMk continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_snd.comp continuous_subtype_val }
  let p : A → V := p₀ ∘ e
  refine ⟨W, V, hW, hW0, hWU, hV, hV0, p, ?_, ?_, ?_, ?_⟩
  · intro z
    exact hp₀ (e z)
  · exact hproper.comp e.isProperMap
  · intro w
    exact Set.Finite.of_finite_image (s := p ⁻¹' {w}) (f := e)
      ((hfinite₀ w).subset (by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hz
        change p₀ (e x) = w
        simpa [p, Function.comp_def] using hx)) e.injective.injOn
  · intro z hz
    have he0 : (e z).val = 0 := hzero (e z) (by
      simpa [p, Function.comp_def] using hz)
    exact congrArg Prod.snd he0

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, I.A and III.C, Cauchy formula and removable singularities; Mathlib.Analysis.Complex.RemovableSingularity. -/
theorem adim6_bounded_point_extension_aux (d : ℕ) (U : Set (Fin (d + 1) → ℂ))
    (hU : IsOpen U) (hU0 : (0 : Fin (d + 1) → ℂ) ∈ U)
    (f : (Fin (d + 1) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hbounded : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    AnalyticOnNhd ℂ (Function.update f 0 (limUnder (𝓝[≠] 0) f)) U := by
  obtain ⟨q, hq, he⟩ := bounded_local_extension U hU hU0 f hf hbounded
  have ht : Tendsto f (𝓝[≠] 0) (𝓝 (q 0)) :=
    (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  have hlim : limUnder (𝓝[≠] 0) f = q 0 := ht.limUnder_eq
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    apply hq.congr
    filter_upwards [eventually_nhdsWithin_iff.mp he] with z hez
    by_cases hz0 : z = 0
    · simp [hz0, hlim]
    · rw [Function.update_of_ne hz0]
      exact (hez hz0).symm
  · apply (hf z ⟨hz, hz0⟩).congr
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    exact (Function.update_of_ne hw _ _).symm

#print axioms adim6_bounded_point_extension_aux

end HodgeLean.Foundations
