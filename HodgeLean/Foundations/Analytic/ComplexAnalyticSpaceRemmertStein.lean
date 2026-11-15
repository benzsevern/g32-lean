import HodgeLean.Foundations.AnalyticGermRSAssembly

/-! # Remmert–Stein extension: helper results

Helpers for `an_remmert_stein_aux`, following Demailly, *Complex Analytic and Differential
Geometry* (2012), II, proof of Theorem 8.7 (step 2): generic linear slicing of the germ
dimension, a projection that is proper over a small ball, bounded symmetric sheet coefficients
continued across the projected exceptional set, and moment observables.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Polynomial

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

open private adim9_krullDim_drop adim9_le_pred_of_succ_le adim9_vanish_of_mem_span
  adim9_point_germ adim9_zeroSet_eq adim9_span_generators adim9_rep adim9_rep_spec
  adim9_cover_eventually adim9_local_hypersurface_extension adim9_pb adim9_pb_rep
  adim9_local_finite_all adim9_ringKrullDim_eq_of_finite_injective
  adim9_injective_of_finite_of_dim adim9_frequently_ne_zero_finset
  adim9_not_locally_zero_ball adim9_local_sheets_at adim9_thin_of_injective_parameters
  adim9_moment_observables_separate adim9_fibre_card_of_sheets
  from HodgeLean.Foundations.AnalyticGermRSAssemblyProofs

/-! ### Linear germs and Krull dimension of germs -/

/-- The germ at the origin of a continuous linear form. -/
private def anr_lin {n : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : AnalyticGerm n :=
  ⟨Germ.ofFun ℓ, ℓ, ℓ.analyticAt 0, rfl⟩

private theorem anr_lin_add {n : ℕ} (ℓ₁ ℓ₂ : (Fin n → ℂ) →L[ℂ] ℂ) :
    anr_lin (ℓ₁ + ℓ₂) = anr_lin ℓ₁ + anr_lin ℓ₂ := Subtype.ext rfl

private theorem anr_lin_smul {n : ℕ} (c : ℂ) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) :
    anr_lin (c • ℓ) = (⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩ :
      AnalyticGerm n) * anr_lin ℓ := Subtype.ext rfl

private theorem anr_lin_zero {n : ℕ} : anr_lin (0 : (Fin n → ℂ) →L[ℂ] ℂ) = 0 :=
  Subtype.ext rfl

/-- Vanishing ideals reverse inclusion of sets. -/
theorem anr_ideal_anti {n : ℕ} {S S' : Set (Fin n → ℂ)} (h : S ⊆ S') (y : Fin n → ℂ) :
    adim2_ideal n (adim2_germ n S' y) ≤ adim2_ideal n (adim2_germ n S y) := by
  intro f hf
  have hf' : adim2_germ n S' y ≤ adim2_zero n f := hf
  change adim2_germ n S y ≤ adim2_zero n f
  refine le_trans ?_ hf'
  change Germ.ofFun (fun z ↦ y + z ∈ S) ≤ Germ.ofFun (fun z ↦ y + z ∈ S')
  exact Germ.coe_le.mpr (Eventually.of_forall fun z hz ↦ h hz)

/-- A larger prime has a smaller quotient dimension. -/
theorem anr_dim_le_of_le {R : Type*} [CommRing R] {Q Q' : Ideal R} (h : Q ≤ Q') :
    ringKrullDim (R ⧸ Q') ≤ ringKrullDim (R ⧸ Q) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

/-- Minimal-prime dimension bounds pass to subsets. -/
theorem anr_dims_mono {n : ℕ} {S S' : Set (Fin n → ℂ)} (h : S' ⊆ S) (y : Fin n → ℂ)
    (d : WithBot ℕ∞)
    (hS : ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ d) :
    ∀ Q' ∈ (adim2_ideal n (adim2_germ n S' y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q') ≤ d := by
  intro Q' hQ'
  have : Q'.IsPrime := hQ'.1.1
  obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le
    ((anr_ideal_anti h y).trans hQ'.1.2)
  exact (anr_dim_le_of_le hQQ').trans (hS Q hQ)

/-- An element of `WithBot ℕ∞` below `e + 1` is at most `e`. -/
theorem anr_le_of_lt_succ (x : WithBot ℕ∞) (e : ℕ) (h : x < ((e + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ (e : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_lt_coe] at h'
      exact absurd h' (not_lt.mpr le_top)
    | coe k =>
      have : k < e + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ e)

/-- Cutting by a level set of a linear form that lies in no top-dimensional minimal prime
lowers every minimal-prime dimension by one. -/
theorem anr_cut {n e : ℕ} (S : Set (Fin n → ℂ)) (y : Fin n → ℂ) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (hle : ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hgood : ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) = ((e + 1 : ℕ) : WithBot ℕ∞) → anr_lin ℓ ∉ Q) :
    ∀ Q' ∈ (adim2_ideal n (adim2_germ n (S ∩ {z | ℓ z = ℓ y}) y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q') ≤ (e : WithBot ℕ∞) := by
  intro Q' hQ'
  have : Q'.IsPrime := hQ'.1.1
  have hsub : adim2_ideal n (adim2_germ n S y) ≤ Q' :=
    (anr_ideal_anti inter_subset_left y).trans hQ'.1.2
  have hℓ : anr_lin ℓ ∈ Q' := by
    apply hQ'.1.2
    change Germ.ofFun (fun z ↦ y + z ∈ S ∩ {z | ℓ z = ℓ y}) ≤
      (Germ.ofFun (fun z : Fin n → ℂ ↦ ℓ z)).map (· = 0)
    rw [Germ.map_coe, Germ.coe_le]
    refine Eventually.of_forall fun z hz ↦ ?_
    have h2 : ℓ (y + z) = ℓ y := hz.2
    rw [map_add] at h2
    simpa using h2
  obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le hsub
  have : Q.IsPrime := hQ.1.1
  by_cases hmem : anr_lin ℓ ∈ Q
  · have hne : ringKrullDim (AnalyticGerm n ⧸ Q) ≠ ((e + 1 : ℕ) : WithBot ℕ∞) :=
      fun h ↦ hgood Q hQ h hmem
    have hlt : ringKrullDim (AnalyticGerm n ⧸ Q) < ((e + 1 : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_ne (hle Q hQ) hne
    exact (anr_dim_le_of_le hQQ').trans (anr_le_of_lt_succ _ e hlt)
  · apply adim9_le_pred_of_succ_le
    exact (adim9_krullDim_drop Q Q' hQQ' (anr_lin ℓ) hmem hℓ).trans (hle Q hQ)

/-- A point at which every minimal prime has dimension zero is isolated. -/
theorem anr_isolated_of_dims {n : ℕ} (S : Set (Fin n → ℂ)) (y : Fin n → ℂ) (hy : y ∈ S)
    (h : ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ (0 : WithBot ℕ∞)) :
    ∀ᶠ z in 𝓝 y, z ∈ S → z = y := by
  let A : Set (Fin n → ℂ) := (fun z ↦ y + z) ⁻¹' S
  have hgerm : adim2_germ n A 0 = adim2_germ n S y := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp [A]
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes (adim9b_germ_ideal_ne_top n S y hy)
  have hQ' : Q ∈ (adim2_ideal n (adim2_germ n A 0)).minimalPrimes := by rwa [hgerm]
  have hlt : ringKrullDim (AnalyticGerm n ⧸ Q) < 1 :=
    lt_of_le_of_lt (h Q hQ) (by exact_mod_cast zero_lt_one)
  have hev := adim9_point_germ n A Q hQ' hlt
  have ht : Tendsto (fun z : Fin n → ℂ ↦ z - y) (𝓝 y) (𝓝 0) := by
    simpa using ((continuous_sub_right y).tendsto y)
  filter_upwards [ht.eventually hev] with z hz hzS
  have := hz (by simpa [A] using hzS)
  exact sub_eq_zero.mp this

/-- The Krull dimension of a quotient is bounded by the bound on its minimal primes.
Source: Matsumura, Commutative Ring Theory, §5. -/
theorem anr_ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (J : Ideal R)
    (d : WithBot ℕ∞) (h : ∀ P ∈ J.minimalPrimes, ringKrullDim (R ⧸ P) ≤ d) :
    ringKrullDim (R ⧸ J) ≤ d := by
  rw [ringKrullDim_quotient, Order.krullDim]
  refine iSup_le fun l ↦ ?_
  have hhead : J ≤ l.head.1.asIdeal := by
    have := l.head.2
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
    exact this
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hhead
  have := hP.1.1
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) P) :=
    ⟨l.length, fun i ↦ ⟨(l i).1, by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
      exact hPle.trans (l.monotone (Fin.zero_le i))⟩, fun i ↦ l.step i⟩
  have := Order.LTSeries.length_le_krullDim l'
  rw [← ringKrullDim_quotient] at this
  exact this.trans (h P hP)

/-- Every minimal prime has dimension at most the dimension of the germ. -/
theorem anr_minimal_le_dim {n : ℕ} (S : adim2_SetGerm n) (Q : Ideal (AnalyticGerm n))
    (hQ : Q ∈ (adim2_ideal n S).minimalPrimes) :
    ringKrullDim (AnalyticGerm n ⧸ Q) ≤ adim2_dimension n S :=
  anr_dim_le_of_le hQ.1.2

/-- A prime containing every linear germ has dimension zero. -/
theorem anr_dim_le_zero_of_linear {n : ℕ} (Q : Ideal (AnalyticGerm n)) (hQ : Q.IsPrime)
    (h : ∀ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, anr_lin ℓ ∈ Q) :
    ringKrullDim (AnalyticGerm n ⧸ Q) ≤ (0 : ℕ) := by
  classical
  have hrep : ∀ g : AnalyticGerm n, Germ.ofFun (adim9_rep g) = g.val :=
    fun g ↦ (adim9_rep_spec g).2
  have hcoord : ∀ i : Fin n, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      (∀ g ∈ adim2_generators n Q, adim9_rep g z = 0) → z i = 0 := by
    intro i
    let ℓ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i
    have hb : anr_lin ℓ ∈ Ideal.span (adim2_generators n Q : Set (AnalyticGerm n)) := by
      rw [adim9_span_generators n Q]
      exact h ℓ
    exact adim9_vanish_of_mem_span n _ adim9_rep hrep (anr_lin ℓ) hb ℓ rfl
  have hsub : adim2_zeroSet n Q ≤ adim2_germ n {0} 0 := by
    rw [adim9_zeroSet_eq n adim9_rep hrep Q]
    apply Germ.coe_le.mpr
    filter_upwards [Filter.eventually_all.mpr hcoord] with z hz hz0
    funext i
    simpa using hz i hz0
  exact adim9b_prime_dimension_le_of_dimH n 0 {0} Q hQ hsub (by simp)

/-! ### Generic points of a component -/

/-- Near a point of a locally analytic set, every component of the germ contains a nonempty
relatively open piece of the set along which the germ of the set is pure of the dimension of
that component, and along which every linear germ of the component vanishes. -/
theorem anr_generic_component {n : ℕ} (S : Set (Fin n → ℂ)) (y : Fin n → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hyU : y ∈ U) (m : ℕ)
    (f : Fin m → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hS : ∀ z ∈ U, (z ∈ S ↔ ∀ j, f j z = 0))
    (Q : Ideal (AnalyticGerm n)) (hQ : Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes)
    (e : ℕ) (hQe : ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (hℓ : anr_lin ℓ ∈ Q)
    (O : Set (Fin n → ℂ)) (hO : O ∈ 𝓝 y) :
    ∃ O₁ : Set (Fin n → ℂ), IsOpen O₁ ∧ O₁ ⊆ O ∧ (O₁ ∩ S).Nonempty ∧ ∀ y₁ ∈ O₁ ∩ S,
      (∀ Q₁ ∈ (adim2_ideal n (adim2_germ n S y₁)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q₁) = (e : WithBot ℕ∞)) ∧
      anr_lin ℓ ∈ adim2_ideal n (adim2_germ n S y₁) := by
  classical
  have hrep : ∀ g : AnalyticGerm n, Germ.ofFun (adim9_rep g) = g.val :=
    fun g ↦ (adim9_rep_spec g).2
  obtain ⟨s, hs⟩ := adim9b_local_equations_of_representatives n m S y U hU hyU f hf hS
  obtain ⟨F, hF, hcover⟩ := adim3_minimal_prime_cover n s
  rw [← hs] at hF hcover
  have hQF : Q ∈ F := by
    have : Q ∈ (F : Set (Ideal (AnalyticGerm n))) := by rw [hF]; exact hQ
    exact this
  have hsubF : ∀ P ∈ F, adim2_zeroSet n P ≤ adim2_germ n S y := fun P hP ↦ by
    rw [hcover]; exact Finset.le_sup hP
  -- the generators of Q and their representatives
  set G := adim2_generators n Q
  let g : Fin G.card → AnalyticGerm n := fun i ↦ (G.equivFin.symm i : AnalyticGerm n)
  have hgen : Ideal.span (Set.range g) = Q := by
    have hr : Set.range g = (G : Set (AnalyticGerm n)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (G.equivFin.symm i).2
      · intro hx
        exact ⟨G.equivFin ⟨x, hx⟩, by simp [g]⟩
    rw [hr]
    exact adim9_span_generators n Q
  -- a ball on which every representative involved is analytic
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      ∀ P ∈ F, ∀ h ∈ adim2_generators n P, AnalyticAt ℂ (adim9_rep h) z := by
    refine (Filter.eventually_all_finset F).mpr fun P _ ↦ ?_
    exact (Filter.eventually_all_finset _).mpr fun h _ ↦
      (adim9_rep_spec h).1.eventually_analyticAt
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hfa : ∀ j, AnalyticOnNhd ℂ (fun z ↦ adim9_rep (g j) z) (Metric.ball 0 ε₀) := by
    intro j z hz
    exact hball₀ z hz Q hQF _ (G.equivFin.symm j).2
  have hQprime : Q.IsPrime := hQ.1.1
  obtain ⟨W, hWo, hW0, hWU, hpure⟩ := adim9b_local_purity n e G.card Q hQprime hQe g hgen
    (fun j z ↦ adim9_rep (g j) z) (Metric.ball 0 ε₀) Metric.isOpen_ball
    (Metric.mem_ball_self hε₀) hfa (fun j ↦ hrep (g j))
  have hvan := adim9_vanish_of_mem_span n G adim9_rep hrep (anr_lin ℓ)
    (by rw [adim9_span_generators n Q]; exact hℓ) ℓ rfl
  have hcov := adim9_cover_eventually S y F hcover hsubF
  have hOt : (fun z ↦ y + z) ⁻¹' O ∈ 𝓝 (0 : Fin n → ℂ) := by
    have hc : ContinuousAt (fun z : Fin n → ℂ ↦ y + z) 0 :=
      continuousAt_const.add continuousAt_id
    exact hc.preimage_mem_nhds (by simpa using hO)
  have hW' : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ W := hWo.mem_nhds hW0
  have hOt' : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), y + z ∈ O := hOt
  have hB' : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball 0 ε₀ := Metric.ball_mem_nhds 0 hε₀
  have hev : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ W ∧
      ((∀ g ∈ G, adim9_rep g z = 0) → ℓ z = 0) ∧
      (y + z ∈ S ↔ ∃ P ∈ F, ∀ g ∈ adim2_generators n P, adim9_rep g z = 0) ∧
      y + z ∈ O ∧ z ∈ Metric.ball 0 ε₀ :=
    hW'.and (hvan.and (hcov.and (hOt'.and hB')))
  obtain ⟨ε, hε, hballε⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨z₀, hz₀, hz₀B⟩ := ((adim9b_frequently_outside_other_components n
    (adim2_germ n S y) F hF hcover Q hQF adim9_rep hrep).and_eventually
      (Metric.ball_mem_nhds (0 : Fin n → ℂ) hε)).exists
  -- the open piece where the other components are absent
  set O' : Set (Fin n → ℂ) := Metric.ball 0 ε ∩
    {z | ∀ P ∈ F.erase Q, ¬ (∀ h ∈ adim2_generators n P, adim9_rep h z = 0)}
  have hO'o : IsOpen O' := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hzε₀ : z ∈ Metric.ball (0 : Fin n → ℂ) ε₀ := (hballε z hz.1).2.2.2.2
    refine inter_mem (Metric.isOpen_ball.mem_nhds hz.1) ?_
    have hP : ∀ P ∈ F.erase Q, ∀ᶠ w in 𝓝 z,
        ¬ (∀ h ∈ adim2_generators n P, adim9_rep h w = 0) := by
      intro P hP
      have hz2 := hz.2 P hP
      push Not at hz2
      obtain ⟨h, hh, hne⟩ := hz2
      have hc := (hball₀ z hzε₀ P (Finset.mem_of_mem_erase hP) h hh).continuousAt
      filter_upwards [hc.eventually_ne hne] with w hw hall'
      exact hw (hall' h hh)
    exact (Filter.eventually_all_finset _).mpr hP
  have hkey : ∀ w ∈ O', (y + w ∈ S ↔ ∀ h ∈ G, adim9_rep h w = 0) := by
    intro w hw
    rw [(hballε w hw.1).2.2.1]
    constructor
    · rintro ⟨P, hPF, hPw⟩
      by_cases hPQ : P = Q
      · subst hPQ; exact hPw
      · exact absurd hPw (hw.2 P (Finset.mem_erase.mpr ⟨hPQ, hPF⟩))
    · intro h
      exact ⟨Q, hQF, h⟩
  have hgG : ∀ w, (∀ j, adim9_rep (g j) w = 0) ↔ ∀ h ∈ G, adim9_rep h w = 0 := by
    intro w
    constructor
    · intro h x hx
      simpa [g] using h (G.equivFin ⟨x, hx⟩)
    · intro h j
      exact h _ (G.equivFin.symm j).2
  refine ⟨(fun x ↦ x - y) ⁻¹' O', hO'o.preimage (continuous_sub_right y), ?_, ?_, ?_⟩
  · intro x hx
    simpa using (hballε (x - y) hx.1).2.2.2.1
  · refine ⟨y + z₀, ?_, ?_⟩
    · show y + z₀ - y ∈ O'
      rw [add_sub_cancel_left]
      exact ⟨hz₀B, hz₀.2⟩
    · exact (hkey z₀ ⟨hz₀B, hz₀.2⟩).mpr hz₀.1
  · rintro y₁ ⟨hy₁O, hy₁S⟩
    set z₁ := y₁ - y
    have hz₁ : z₁ ∈ O' := hy₁O
    have hyz : y + z₁ = y₁ := by simp [z₁]
    have hnear : ∀ᶠ w in 𝓝 (0 : Fin n → ℂ), z₁ + w ∈ O' := by
      have hc : ContinuousAt (fun w : Fin n → ℂ ↦ z₁ + w) 0 :=
        continuousAt_const.add continuousAt_id
      exact hc.preimage_mem_nhds (by simpa using hO'o.mem_nhds hz₁)
    have hloc : ∀ w, z₁ + w ∈ O' → (y₁ + w ∈ S ↔ ∀ h ∈ G, adim9_rep h (z₁ + w) = 0) := by
      intro w hw
      rw [← hkey _ hw, ← hyz, add_assoc]
    set Z : Set (Fin n → ℂ) := {z | ∀ j, adim9_rep (g j) z = 0}
    have hgerm : adim2_germ n S y₁ = adim2_germ n Z z₁ := by
      apply Germ.coe_eq.mpr
      filter_upwards [hnear] with w hw
      apply propext
      rw [hloc w hw]
      exact (hgG _).symm
    have hz₁S : ∀ h ∈ G, adim9_rep h z₁ = 0 := by
      have := (hloc 0 (by simpa using hz₁)).mp (by simpa using hy₁S)
      simpa using this
    refine ⟨?_, ?_⟩
    · intro Q₁ hQ₁
      rw [hgerm] at hQ₁
      exact hpure z₁ (hballε z₁ hz₁.1).1 ((hgG z₁).mpr hz₁S) Q₁ hQ₁
    · have hℓz₁ : ℓ z₁ = 0 := (hballε z₁ hz₁.1).2.1 hz₁S
      change Germ.ofFun (fun w ↦ y₁ + w ∈ S) ≤
        (Germ.ofFun (fun w : Fin n → ℂ ↦ ℓ w)).map (· = 0)
      rw [Germ.map_coe, Germ.coe_le]
      filter_upwards [hnear] with w hw hwS
      have h1 := (hballε (z₁ + w) hw.1).2.1 ((hloc w hw).mp hwS)
      rw [map_add, hℓz₁, zero_add] at h1
      exact h1

/-- A Krull dimension of a nontrivial ring bounded by a natural number is a natural number. -/
theorem anr_dim_cases {R : Type*} [CommRing R] [Nontrivial R] (e : ℕ)
    (h : ringKrullDim R ≤ (e : WithBot ℕ∞)) : ∃ k : ℕ, k ≤ e ∧ ringKrullDim R = k := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := R)
  generalize ringKrullDim R = x at h h0 ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((e : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe] at h'
      exact absurd h' (by simp)
    | coe k =>
      exact ⟨k, by exact_mod_cast h, rfl⟩

/-- A locally analytic set of constant germ dimension is pure: every minimal prime of every
germ has that dimension. -/
theorem anr_pure_of_dim {n : ℕ} (S : Set (Fin n → ℂ))
    (hloc : ∀ y ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S ↔ ∀ j, f j z = 0))
    (e : ℕ) (hdim : ∀ y ∈ S, adim2_dimension n (adim2_germ n S y) = (e : WithBot ℕ∞)) :
    ∀ y ∈ S, ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞) := by
  intro y hy Q hQ
  have : Q.IsPrime := hQ.1.1
  have hle : ringKrullDim (AnalyticGerm n ⧸ Q) ≤ (e : WithBot ℕ∞) :=
    (anr_minimal_le_dim _ Q hQ).trans (hdim y hy).le
  obtain ⟨k, hke, hk⟩ := anr_dim_cases e hle
  by_cases hkeq : k = e
  · rw [hk, hkeq]
  exfalso
  obtain ⟨U, hU, hyU, m, f, hf, hS⟩ := hloc y hy
  obtain ⟨O₁, -, -, ⟨y₁, hy₁O, hy₁S⟩, hO₁⟩ := anr_generic_component S y U hU hyU m f hf hS Q hQ
    k hk 0 (by rw [anr_lin_zero]; exact Q.zero_mem) univ univ_mem
  have hall := (hO₁ y₁ ⟨hy₁O, hy₁S⟩).1
  have hdle : adim2_dimension n (adim2_germ n S y₁) ≤ (k : WithBot ℕ∞) :=
    anr_ringKrullDim_quotient_le_of_minimalPrimes _ _ fun P hP ↦ (hall P hP).le
  rw [hdim y₁ hy₁S] at hdle
  have : e ≤ k := by exact_mod_cast hdle
  omega

/-- Countably many points of a locally analytic set detect every linear germ lying in a
component of a given dimension at some point. -/
theorem anr_countable_bad {n : ℕ} (S : Set (Fin n → ℂ))
    (hloc : ∀ y ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S ↔ ∀ j, f j z = 0)) :
    ∃ C : Set (Fin n → ℂ), C.Countable ∧ C ⊆ S ∧ ∀ y ∈ S, ∀ (e : ℕ)
      (ℓ : (Fin n → ℂ) →L[ℂ] ℂ), ∀ Q ∈ (adim2_ideal n (adim2_germ n S y)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞) → anr_lin ℓ ∈ Q →
        ∃ y₁ ∈ C, ∃ Q₁ ∈ (adim2_ideal n (adim2_germ n S y₁)).minimalPrimes,
          ringKrullDim (AnalyticGerm n ⧸ Q₁) = (e : WithBot ℕ∞) ∧ anr_lin ℓ ∈ Q₁ := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense S
  refine ⟨Subtype.val '' s, hsc.image _, by rintro _ ⟨x, -, rfl⟩; exact x.2, ?_⟩
  intro y hy e ℓ Q hQ hQe hℓ
  obtain ⟨U, hU, hyU, m, f, hf, hS⟩ := hloc y hy
  obtain ⟨O₁, hO₁o, -, ⟨y₀, hy₀O, hy₀S⟩, hO₁⟩ := anr_generic_component S y U hU hyU m f hf hS
    Q hQ e hQe ℓ hℓ univ univ_mem
  obtain ⟨⟨y₁, hy₁S⟩, hy₁O, hy₁s⟩ := hsd.inter_open_nonempty (Subtype.val ⁻¹' O₁)
    (hO₁o.preimage continuous_subtype_val) ⟨⟨y₀, hy₀S⟩, hy₀O⟩
  obtain ⟨hpure, hlin⟩ := hO₁ y₁ ⟨hy₁O, hy₁S⟩
  obtain ⟨Q₁, hQ₁⟩ := Ideal.nonempty_minimalPrimes (adim9b_germ_ideal_ne_top n S y₁ hy₁S)
  exact ⟨y₁, ⟨⟨y₁, hy₁S⟩, hy₁s, rfl⟩, Q₁, hQ₁, hpure Q₁ hQ₁, hQ₁.1.2 hlin⟩

/-- The linear forms whose germ lies in a given ideal. -/
private def anr_linSub {n : ℕ} (Q : Ideal (AnalyticGerm n)) :
    Submodule ℂ ((Fin n → ℂ) →L[ℂ] ℂ) where
  carrier := {ℓ | anr_lin ℓ ∈ Q}
  add_mem' := by
    intro a b ha hb
    change anr_lin (a + b) ∈ Q
    rw [anr_lin_add]
    exact Q.add_mem ha hb
  zero_mem' := by
    change anr_lin 0 ∈ Q
    rw [anr_lin_zero]
    exact Q.zero_mem
  smul_mem' := by
    intro c a ha
    change anr_lin (c • a) ∈ Q
    rw [anr_lin_smul]
    exact Q.mul_mem_left _ ha

/-- A single linear form avoids every top-dimensional component of every germ of countably
many locally analytic sets of positive dimension. -/
theorem anr_avoid {n : ℕ} {ι : Type*} [Countable ι] (S : ι → Set (Fin n → ℂ)) (e : ι → ℕ)
    (he : ∀ i, 1 ≤ e i)
    (hloc : ∀ i, ∀ y ∈ S i, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S i ↔ ∀ j, f j z = 0)) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, ∀ i, ∀ y ∈ S i,
      ∀ Q ∈ (adim2_ideal n (adim2_germ n (S i) y)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q) = (e i : WithBot ℕ∞) → anr_lin ℓ ∉ Q := by
  classical
  choose C hCc hCS hC using fun i ↦ anr_countable_bad (S i) (hloc i)
  let J := Σ i, Σ y : C i, {Q // Q ∈ (adim2_ideal n (adim2_germ n (S i) y)).minimalPrimes ∧
    ringKrullDim (AnalyticGerm n ⧸ Q) = (e i : WithBot ℕ∞)}
  have : ∀ i, Countable (C i) := fun i ↦ (hCc i).to_subtype
  have : ∀ i (y : C i), Countable {Q // Q ∈ (adim2_ideal n (adim2_germ n (S i) y)).minimalPrimes ∧
      ringKrullDim (AnalyticGerm n ⧸ Q) = (e i : WithBot ℕ∞)} := by
    intro i y
    have hfin : (adim2_ideal n (adim2_germ n (S i) y)).minimalPrimes.Finite := by
      have := adim_noetherian n
      exact Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
    exact ((hfin.subset fun Q hQ ↦ hQ.1).countable).to_subtype
  have hJ : Countable J := inferInstance
  let M : J → Submodule ℂ ((Fin n → ℂ) →L[ℂ] ℂ) := fun j ↦ anr_linSub j.2.2.1
  have hproper : ∀ j, M j ≠ ⊤ := by
    intro j htop
    have hQ := j.2.2.2
    have : j.2.2.1.IsPrime := hQ.1.1.1
    have h0 := anr_dim_le_zero_of_linear j.2.2.1 this fun ℓ ↦ by
      have : ℓ ∈ M j := htop ▸ Submodule.mem_top
      exact this
    rw [hQ.2] at h0
    have : e j.1 ≤ 0 := by exact_mod_cast h0
    have := he j.1
    omega
  by_contra hno
  push Not at hno
  have hcover : ⋃ j, (M j : Set ((Fin n → ℂ) →L[ℂ] ℂ)) = univ := by
    refine eq_univ_of_forall fun ℓ ↦ ?_
    obtain ⟨i, y, hy, Q, hQ, hQe, hℓ⟩ := hno ℓ
    obtain ⟨y₁, hy₁, Q₁, hQ₁, hQ₁e, hℓ₁⟩ := hC i y hy (e i) ℓ Q hQ hQe hℓ
    exact mem_iUnion.mpr ⟨⟨i, ⟨y₁, hy₁⟩, ⟨Q₁, hQ₁, hQ₁e⟩⟩, hℓ₁⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed
    (fun j ↦ Submodule.closed_of_finiteDimensional (M j)) hcover
  exact hproper j (Submodule.eq_top_of_nonempty_interior' _ hj)

/-- Adding finitely many globally analytic equations keeps local equations. -/
theorem anr_loc_inter {n : ℕ} (S : Set (Fin n → ℂ)) (y : Fin n → ℂ)
    (hloc : ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S ↔ ∀ j, f j z = 0))
    (k : ℕ) (g : Fin k → (Fin n → ℂ) → ℂ) (hg : ∀ j, AnalyticOnNhd ℂ (g j) univ) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S ∩ {z | ∀ j, g j z = 0} ↔ ∀ j, f j z = 0) := by
  obtain ⟨U, hU, hyU, m, f, hf, hS⟩ := hloc
  refine ⟨U, hU, hyU, m + k, Fin.append f g, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa using hf i
    · simpa using (hg i).mono (subset_univ U)
  · intro z hz
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right, mem_inter_iff, mem_ofPred_eq, hS z hz]

/-- Linear level sets as common zeros of finitely many analytic functions. -/
theorem anr_level_eq {n p : ℕ} (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (b : Fin n → ℂ) :
    {z | ξ z = ξ b} = {z | ∀ j : Fin p, ξ z j - ξ b j = 0} := by
  ext z
  simp only [mem_ofPred_eq, sub_eq_zero]
  exact funext_iff

theorem anr_level_analytic {n p : ℕ} (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (b : Fin n → ℂ) :
    ∀ j : Fin p, AnalyticOnNhd ℂ (fun z ↦ ξ z j - ξ b j) univ := by
  intro j z _
  exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) j).comp ξ).analyticAt
    z).sub analyticAt_const

/-- Appending a linear form to a linear map to `Fin p → ℂ`. -/
private def anr_snoc {n p : ℕ} (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin (p + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.snoc (α := fun _ ↦ (Fin n → ℂ) →L[ℂ] ℂ)
    (fun k ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) k).comp ξ) ℓ)

private theorem anr_snoc_eq {n p : ℕ} (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (z b : Fin n → ℂ) :
    anr_snoc ξ ℓ z = anr_snoc ξ ℓ b ↔ ξ z = ξ b ∧ ℓ z = ℓ b := by
  constructor
  · intro h
    refine ⟨funext fun k ↦ ?_, ?_⟩
    · have := congrFun h (Fin.castSucc k)
      simpa [anr_snoc] using this
    · have := congrFun h (Fin.last p)
      simpa [anr_snoc] using this
  · rintro ⟨h1, h2⟩
    funext j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [anr_snoc] using h2
    · simp [anr_snoc, h1]

/-- Generic linear slicing: for countably many locally analytic sets with base points, there
is a linear map to `ℂ^p` whose level set through each base point cuts the set in a germ of
dimension at most the original bound minus `p` at each of its points. -/
theorem anr_slice {n : ℕ} {ι : Type*} [Countable ι] (S : ι → Set (Fin n → ℂ))
    (b : ι → Fin n → ℂ) (e : ι → ℕ)
    (hloc : ∀ i, ∀ y ∈ S i, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S i ↔ ∀ j, f j z = 0))
    (hdim : ∀ i, ∀ y ∈ S i, ∀ Q ∈ (adim2_ideal n (adim2_germ n (S i) y)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ (e i : WithBot ℕ∞)) :
    ∀ p : ℕ, ∃ ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ), ∀ i, ∀ y ∈ S i ∩ {z | ξ z = ξ (b i)},
      ∀ Q ∈ (adim2_ideal n (adim2_germ n (S i ∩ {z | ξ z = ξ (b i)}) y)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q) ≤ ((e i - p : ℕ) : WithBot ℕ∞) := by
  intro p
  induction p with
  | zero =>
    refine ⟨0, fun i y hy Q hQ ↦ ?_⟩
    rw [Nat.sub_zero]
    exact anr_dims_mono inter_subset_left y _ (hdim i y hy.1) Q hQ
  | succ p ih =>
    obtain ⟨ξ, hξ⟩ := ih
    set S' : ι → Set (Fin n → ℂ) := fun i ↦ S i ∩ {z | ξ z = ξ (b i)}
    have hloc' : ∀ i, ∀ y ∈ S' i, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
        (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
          ∀ z ∈ U, (z ∈ S' i ↔ ∀ j, f j z = 0) := by
      intro i y hy
      have := anr_loc_inter (S i) y (hloc i y hy.1) p _ (anr_level_analytic ξ (b i))
      simpa only [S', anr_level_eq ξ (b i)] using this
    let ι' := {i // 1 ≤ e i - p}
    obtain ⟨ℓ, hℓ⟩ := anr_avoid (ι := ι') (fun i ↦ S' i.1) (fun i ↦ e i.1 - p) (fun i ↦ i.2)
      (fun i ↦ hloc' i.1)
    refine ⟨anr_snoc ξ ℓ, fun i y hy Q hQ ↦ ?_⟩
    have hset : ∀ c : Fin n → ℂ, S i ∩ {z | anr_snoc ξ ℓ z = anr_snoc ξ ℓ c} =
        (S i ∩ {z | ξ z = ξ c}) ∩ {z | ℓ z = ℓ c} := by
      intro c
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, anr_snoc_eq]
      tauto
    rw [hset] at hy hQ
    have hyS' : y ∈ S' i := hy.1
    have hℓy : ℓ y = ℓ (b i) := hy.2
    rw [← hℓy] at hQ
    by_cases hei : 1 ≤ e i - p
    · obtain ⟨e₀, he₀⟩ : ∃ e₀, e i - p = e₀ + 1 := ⟨e i - p - 1, by omega⟩
      have hbound := hξ i y hyS'
      rw [he₀] at hbound
      have := anr_cut (e := e₀) (S' i) y ℓ hbound (fun Q' hQ' hQ'e ↦ hℓ ⟨i, hei⟩ y hyS' Q' hQ'
        (by simpa [he₀] using hQ'e)) Q hQ
      have heq : e i - (p + 1) = e₀ := by omega
      rw [heq]
      exact this
    · have heq : e i - (p + 1) = 0 := by omega
      have h0 : e i - p = 0 := by omega
      have := anr_dims_mono (S := S' i) inter_subset_left y _ (hξ i y hyS') Q hQ
      rw [heq]
      rw [h0] at this
      exact this

/-! ### A box on which the projection is proper -/

/-- A closed set avoiding the sphere of radius `R` in the fibre through `a` stays a positive
distance away in the base along that sphere. -/
theorem anr_box_radius {n p : ℕ} (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (a : Fin n → ℂ) (R : ℝ)
    (hsph : ∀ z ∈ K, ξ z = ξ a → ‖z - a‖ ≠ R) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖ := by
  set S := K ∩ Metric.sphere a R
  have hS : IsCompact S := (isCompact_sphere a R).inter_left hK
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz hzR ↦ ?_⟩
    have : z ∈ S := ⟨hz, by simpa [dist_eq_norm] using hzR⟩
    rw [hSe] at this
    exact absurd this (notMem_empty z)
  obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hSne
    ((ξ.continuous.sub continuous_const).norm.continuousOn)
  have hz₀R : ‖z₀ - a‖ = R := by simpa [dist_eq_norm] using hz₀.2
  refine ⟨‖ξ z₀ - ξ a‖, ?_, fun z hz hzR ↦ ?_⟩
  · rw [norm_pos_iff, sub_ne_zero]
    exact fun h ↦ hsph z₀ hz₀.1 h hz₀R
  · exact hmin ⟨hz, by simpa [dist_eq_norm] using hzR⟩

/-- Fibres of a closed set over the base ball, inside the box, are compact. -/
theorem anr_box_fibre_compact {n p : ℕ} (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (a : Fin n → ℂ) (R r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ)
    (hw : ‖w - ξ a‖ < r) :
    IsCompact {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} := by
  have heq : {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} =
      K ∩ Metric.closedBall a R ∩ ξ ⁻¹' {w} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_eq_norm,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨⟨hz, hzR.le⟩, hzw⟩
    · rintro ⟨⟨hz, hzR⟩, hzw⟩
      refine ⟨hz, lt_of_le_of_ne hzR fun h ↦ ?_, hzw⟩
      have := hsph z hz h
      rw [hzw] at this
      linarith
  rw [heq]
  exact ((isCompact_closedBall a R).inter_left hK).inter_right
    (isClosed_singleton.preimage ξ.continuous)

/-- The tube lemma for the box: if the fibre over `w` lies in an open set, so do the fibres
over all parameters near `w`. -/
theorem anr_box_tube {n p : ℕ} (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (a : Fin n → ℂ) (R r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ)
    (hw : ‖w - ξ a‖ < r) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (hfib : ∀ z ∈ K, ‖z - a‖ < R → ξ z = w → z ∈ O) :
    ∀ᶠ v in 𝓝 w, ∀ z ∈ K, ‖z - a‖ < R → ξ z = v → z ∈ O := by
  obtain ⟨ε, hε, hεr⟩ : ∃ ε > 0, ‖w - ξ a‖ + ε < r := ⟨(r - ‖w - ξ a‖) / 2, by linarith,
    by linarith⟩
  set Kc := K ∩ Metric.closedBall a R ∩ ξ ⁻¹' Metric.closedBall w ε
  have hKc : IsCompact Kc := ((isCompact_closedBall a R).inter_left hK).inter_right
    (Metric.isClosed_closedBall.preimage ξ.continuous)
  have hKO : IsCompact (Kc \ O) := hKc.diff hO
  have himg : IsClosed (ξ '' (Kc \ O)) := (hKO.image ξ.continuous).isClosed
  have hwn : w ∉ ξ '' (Kc \ O) := by
    rintro ⟨z, ⟨⟨⟨hzK, hzR⟩, -⟩, hzO⟩, hzw⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hzR
    rcases hzR.lt_or_eq with hlt | heq
    · exact hzO (hfib z hzK hlt hzw)
    · have := hsph z hzK heq
      rw [hzw] at this
      linarith
  filter_upwards [Metric.ball_mem_nhds w hε, himg.isOpen_compl.mem_nhds hwn] with v hv hvn
    z hzK hzR hzv
  by_contra hzO
  apply hvn
  refine ⟨z, ⟨⟨⟨hzK, ?_⟩, ?_⟩, hzO⟩, hzv⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hzR.le
  · rw [mem_preimage, hzv]
    exact Metric.ball_subset_closedBall hv

/-! ### Sets lying locally in hypersurfaces -/

/-- The complement of a set lying locally in nowhere locally zero hypersurfaces is dense. -/
theorem anr_thin_dense {d : ℕ} (V A : Set (Fin d → ℂ))
    (hA : ∀ x ∈ V, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ A ∩ W ⊆ {y | δ y = 0}) :
    V ⊆ closure (V \ A) := by
  intro x hx
  obtain ⟨W, hWo, hxW, hWV, δ, -, hnz, hAW⟩ := hA x hx
  rw [mem_closure_iff_frequently]
  exact ((Filter.not_eventually.mp (hnz x hxW)).and_eventually (hWo.mem_nhds hxW)).mono
    fun v hv ↦ ⟨hWV hv.2, fun hvA ↦ hv.1 (hAW ⟨hvA, hv.2⟩)⟩

/-- Bounded analytic functions continue across a relatively closed set lying locally in
hypersurfaces, followed by a set lying locally in hypersurfaces of its complement. -/
theorem anr_thin2_extension {d : ℕ} (V A E : Set (Fin (d + 1) → ℂ))
    (hA : ∀ x ∈ V, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ A ∩ W ⊆ {y | δ y = 0})
    (hE : ∀ x ∈ V \ A, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V \ A ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (f : (Fin (d + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f ((V \ A) \ E))
    (M : ℝ) (hb : ∀ x ∈ (V \ A) \ E, ‖f x‖ ≤ M) :
    ∃ F : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ F V ∧ EqOn F f ((V \ A) \ E) ∧
      ∀ x ∈ V, ‖F x‖ ≤ M := by
  obtain ⟨F₁, hF₁, hF₁f, hF₁b⟩ := adim9_local_hypersurface_extension d (V \ A) E hE f hf M hb
  obtain ⟨F, hF, hFF₁, hFb⟩ := adim9_local_hypersurface_extension d V A hA F₁ hF₁ M hF₁b
  exact ⟨F, hF, fun x hx ↦ (hFF₁ hx.1).trans (hF₁f hx), hFb⟩

/-- The complement of such a pair of sets is dense. -/
theorem anr_thin2_dense {d : ℕ} (V A E : Set (Fin d → ℂ))
    (hA : ∀ x ∈ V, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ A ∩ W ⊆ {y | δ y = 0})
    (hE : ∀ x ∈ V \ A, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V \ A ∧
      ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0}) :
    V ⊆ closure ((V \ A) \ E) := by
  intro x hx
  have h1 := anr_thin_dense V A hA hx
  have h2 : closure (V \ A) ⊆ closure ((V \ A) \ E) := by
    rw [← closure_closure (s := (V \ A) \ E)]
    exact closure_mono (anr_thin_dense (V \ A) E hE)
  exact h2 h1

/-- The complement of such a pair of sets in a preconnected open set is preconnected. -/
theorem anr_thin2_preconnected {d : ℕ} (V A E : Set (Fin (d + 1) → ℂ))
    (hV : IsPreconnected V)
    (hA : ∀ x ∈ V, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ A ∩ W ⊆ {y | δ y = 0})
    (hE : ∀ x ∈ V \ A, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V \ A ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (hD : IsOpen ((V \ A) \ E)) :
    IsPreconnected ((V \ A) \ E) := by
  classical
  set D := (V \ A) \ E
  have hdense : V ⊆ closure D := anr_thin2_dense V A E hA hE
  intro u v hu hv hDuv hDu hDv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hdisj : ∀ x ∈ D, x ∈ u → x ∈ v → False := fun x hx hxu hxv ↦ by
    have : x ∈ D ∩ (u ∩ v) := ⟨hx, hxu, hxv⟩
    rw [hne] at this
    exact this
  let g : (Fin (d + 1) → ℂ) → ℂ := fun z ↦ if z ∈ D ∩ u then 1 else 0
  have hg : AnalyticOnNhd ℂ g D := by
    intro x hx
    rcases hDuv hx with hxu | hxv
    · refine (analyticAt_const (v := (1 : ℂ))).congr ?_
      filter_upwards [(hD.inter hu).mem_nhds ⟨hx, hxu⟩] with z hz
      show (1 : ℂ) = if z ∈ D ∩ u then 1 else 0
      rw [ite_eq_left_iff.mpr (fun h ↦ absurd hz h)]
    · refine (analyticAt_const (v := (0 : ℂ))).congr ?_
      filter_upwards [(hD.inter hv).mem_nhds ⟨hx, hxv⟩] with z hz
      have : z ∉ D ∩ u := fun h ↦ hdisj z hz.1 h.2 hz.2
      show (0 : ℂ) = if z ∈ D ∩ u then 1 else 0
      rw [ite_eq_right_iff.mpr (fun h ↦ absurd h this)]
  have hgb : ∀ x ∈ D, ‖g x‖ ≤ 1 := by
    intro x _
    simp only [g]
    split_ifs <;> simp
  obtain ⟨G, hG, hGg, -⟩ := anr_thin2_extension V A E hA hE g hg 1 hgb
  have hGD : ∀ x ∈ D, G x * (G x - 1) = 0 := by
    intro x hx
    rw [hGg hx]
    simp only [g]
    split_ifs <;> simp
  have hGV : ∀ x ∈ V, G x ∈ ({0, 1} : Set ℂ) := by
    intro x hx
    have hc : ContinuousWithinAt (fun z ↦ G z * (G z - 1)) D x :=
      ((hG x hx).continuousAt.mul ((hG x hx).continuousAt.sub continuousAt_const)
        ).continuousWithinAt
    have h0 := hc.eq_const_of_mem_closure (hdense hx) hGD
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  obtain ⟨x₁, hx₁D, hx₁u⟩ := hDu
  obtain ⟨x₂, hx₂D, hx₂v⟩ := hDv
  have hconst := hV.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr inferInstance)
    (fun x hx ↦ (hG x hx).continuousAt.continuousWithinAt) hGV
    hx₁D.1.1 hx₂D.1.1
  rw [hGg hx₁D, hGg hx₂D] at hconst
  have h2 : x₂ ∉ D ∩ u := fun h ↦ hdisj x₂ hx₂D h.2 hx₂v
  have h1 : x₁ ∈ D ∩ u := ⟨hx₁D, hx₁u⟩
  simp only [g, h1, h2, ite_true, ite_false] at hconst
  exact one_ne_zero hconst

/-! ### The projected exceptional set lies locally in hypersurfaces -/

/-- Local equations of the part of a fibre inside a ball. -/
theorem anr_fibre_loc {n p : ℕ} (S : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (hloc : ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S ↔ ∀ j, f j z = 0))
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (w : Fin p → ℂ) (a : Fin n → ℂ) (R : ℝ)
    (hx : ‖x - a‖ < R) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ {z | z ∈ S ∧ ‖z - a‖ < R ∧ ξ z = w} ↔ ∀ j, f j z = 0) := by
  obtain ⟨U, hU, hxU, m, f, hf, hS⟩ := hloc
  have hball : IsOpen {z : Fin n → ℂ | ‖z - a‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  refine ⟨U ∩ {z | ‖z - a‖ < R}, hU.inter hball, ⟨hxU, hx⟩, m + p,
    Fin.append f (fun k z ↦ ξ z k - w k), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) j
    · simpa using (hf i).mono inter_subset_left
    · simp only [Fin.append_right]
      intro z _
      exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) k).comp ξ).analyticAt
        z).sub analyticAt_const
  · intro z hz
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right, mem_ofPred_eq, ← hS z hz.1, sub_eq_zero]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, fun k ↦ congrFun h3 k⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, hz.2, funext h3⟩

/-- At a point of a set of dimension at most `d` that is isolated in its fibre, some nonzero
analytic function on the base `ℂ^(d+1)` vanishes on the projection of the nearby part of the
set. -/
theorem anr_image_thin_at (N d : ℕ) (T : Set (Fin (N + 1) → ℂ)) (y : Fin (N + 1) → ℂ)
    (hy : y ∈ T) (U : Set (Fin (N + 1) → ℂ)) (hU : IsOpen U) (hyU : y ∈ U) (m : ℕ)
    (f : Fin m → (Fin (N + 1) → ℂ) → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hUT : ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y' in 𝓝 y, y' ∈ T → ξ y' = ξ y → y' = y)
    (hdim : ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞)) :
    ∃ (O : Set (Fin (N + 1) → ℂ)) (ρ : ℝ) (δ : (Fin (d + 1) → ℂ) → ℂ), IsOpen O ∧ y ∈ O ∧
      0 < ρ ∧ AnalyticOnNhd ℂ δ (Metric.ball (ξ y) ρ) ∧
      (∀ w ∈ Metric.ball (ξ y) ρ, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ z ∈ T ∩ O, δ (ξ z) = 0 := by
  classical
  have : NoZeroDivisors (AnalyticGerm (d + 1)) := analyticGerm_noZeroDivisors_succ
  have : Nontrivial (AnalyticGerm (d + 1)) := (analyticGermValue (d + 1)).domain_nontrivial
  set I := adim2_ideal (N + 1) (adim2_germ (N + 1) T y)
  have hfin := adim9_local_finite_all N d T y hy U hU hyU m f hf hUT ξ hiso
  have hker : ∀ P ∈ I.minimalPrimes, ∃ a : AnalyticGerm (d + 1), a ≠ 0 ∧ adim9_pb ξ a ∈ P := by
    intro P hP
    have : P.IsPrime := hP.1.1
    by_contra hno
    push Not at hno
    have hinj : Function.Injective ((Ideal.Quotient.mk P).comp (adim9_pb ξ)) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra ha0
      exact hno a ha0 (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    have heq := adim9_ringKrullDim_eq_of_finite_injective _ (hfin P hP) hinj
    rw [adim6_parameter_dimension (d + 1)] at heq
    have h2 := hdim P hP
    rw [← heq] at h2
    have : d + 1 ≤ d := by exact_mod_cast h2
    omega
  have hIfin : I.minimalPrimes.Finite := by
    have := adim_noetherian (N + 1)
    exact Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  choose! a ha0 haP using hker
  set Fs := hIfin.toFinset
  set h : AnalyticGerm (d + 1) := ∏ P ∈ Fs, a P
  have hh0 : h ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP ↦
    ha0 P ((Set.Finite.mem_toFinset _).mp hP)
  have hhI : adim9_pb ξ h ∈ I := by
    have h1 : adim9_pb ξ h ∈ ∏ P ∈ Fs, P := by
      rw [map_prod]
      exact Ideal.prod_mem_prod fun P hP ↦ haP P ((Set.Finite.mem_toFinset _).mp hP)
    have h2 : (∏ P ∈ Fs, P) ≤ I := by
      refine Ideal.prod_le_inf.trans ?_
      have hrad : I.radical = I := adim2_radical (N + 1) (adim2_germ (N + 1) T y)
      rw [← hrad, ← Ideal.sInf_minimalPrimes]
      exact le_sInf fun P hP ↦ Finset.inf_le (f := fun P ↦ P)
        ((Set.Finite.mem_toFinset _).mpr hP)
    exact h2 h1
  set H := adim9_rep h
  obtain ⟨hHa, hHrep⟩ := adim9_rep_spec h
  have hvan : ∀ᶠ z in 𝓝 (0 : Fin (N + 1) → ℂ), y + z ∈ T → H (ξ z) = 0 := by
    have : adim2_germ (N + 1) T y ≤ (adim9_pb ξ h).val.map (· = 0) := hhI
    rw [← adim9_pb_rep ξ h H hHrep, Germ.map_coe] at this
    exact Germ.coe_le.mp this
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.mp hvan
  obtain ⟨ρ, hρ, hballρ⟩ := Metric.eventually_nhds_iff_ball.mp hHa.eventually_analyticAt
  have hH0 : ¬ (H =ᶠ[𝓝 0] fun _ ↦ 0) := by
    intro hz
    apply hh0
    apply Subtype.ext
    rw [← hHrep]
    exact Germ.coe_eq.mpr hz
  have hHnz := adim9_not_locally_zero_ball H ρ hballρ hH0
  refine ⟨(fun z ↦ z - y) ⁻¹' Metric.ball 0 ε₁, ρ, fun w ↦ H (w - ξ y),
    Metric.isOpen_ball.preimage (continuous_sub_right y), by simp [hε₁], hρ, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w - ξ y ∈ Metric.ball (0 : Fin (d + 1) → ℂ) ρ := by
      rwa [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
    exact (hballρ _ hw').comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  · intro w hw hev
    have hw' : w - ξ y ∈ Metric.ball (0 : Fin (d + 1) → ℂ) ρ := by
      rwa [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
    apply hHnz _ hw'
    have ht : Tendsto (fun u : Fin (d + 1) → ℂ ↦ u + ξ y) (𝓝 (w - ξ y)) (𝓝 w) := by
      have hc : Continuous (fun u : Fin (d + 1) → ℂ ↦ u + ξ y) :=
        continuous_id.add continuous_const
      simpa using hc.tendsto (w - ξ y)
    filter_upwards [ht.eventually hev] with u hu
    simpa using hu
  · rintro z ⟨hzT, hzO⟩
    have := hball₁ (z - y) hzO (by simpa using hzT)
    simpa [map_sub] using this

/-- The projection into the base ball of the part of a set of dimension at most `d` inside the
box lies locally in nowhere locally zero hypersurfaces, and is relatively closed. -/
theorem anr_image_thin (N d : ℕ) (T : Set (Fin (N + 1) → ℂ)) (hTc : IsClosed T)
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (a : Fin (N + 1) → ℂ) (R r : ℝ)
    (hsph : ∀ z ∈ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) :
    (∀ x ∈ Metric.ball (ξ a) r, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
      W ⊆ Metric.ball (ξ a) r ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧
        ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r} ∩ W ⊆ {y | δ y = 0}) ∧
    IsOpen (Metric.ball (ξ a) r \ ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}) := by
  classical
  set A := ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}
  have hballR : IsOpen {z : Fin (N + 1) → ℂ | ‖z - a‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have hx' : ‖x - ξ a‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    set Fx := {z | z ∈ T ∧ ‖z - a‖ < R ∧ ξ z = x}
    have hFxc : IsCompact Fx := anr_box_fibre_compact T hTc ξ a R r hsph x hx'
    have hFxf : Fx.Finite := adim9_compact_analytic_finite (N + 1) Fx hFxc fun z hz ↦
      anr_fibre_loc T z (hTloc z hz.1) ξ x a R hz.2.1
    have hiso : ∀ y ∈ Fx, ∀ᶠ y' in 𝓝 y, y' ∈ T → ξ y' = ξ y → y' = y := by
      intro y hy
      have hcl : IsClosed (Fx \ {y}) := (hFxf.subset sdiff_subset).isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl),
        hballR.mem_nhds hy.2.1] with y' hy' hy'R hy'T hξ
      by_contra hne
      exact hy' ⟨⟨hy'T, hy'R, hξ.trans hy.2.2⟩, hne⟩
    have hdata : ∀ y ∈ Fx, ∃ (O : Set (Fin (N + 1) → ℂ)) (ρ : ℝ)
        (δ : (Fin (d + 1) → ℂ) → ℂ), IsOpen O ∧ y ∈ O ∧
        0 < ρ ∧ AnalyticOnNhd ℂ δ (Metric.ball (ξ y) ρ) ∧
        (∀ w ∈ Metric.ball (ξ y) ρ, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
        ∀ z ∈ T ∩ O, δ (ξ z) = 0 := by
      intro y hy
      obtain ⟨U, hU, hyU, m, f, hf, hUT⟩ := hTloc y hy.1
      exact anr_image_thin_at N d T y hy.1 U hU hyU m f hf hUT ξ (hiso y hy) (hdimT y hy.1)
    choose! O ρ δ hOo hyO hρ hδ hnz hvan using hdata
    set Fs := hFxf.toFinset
    have hFs : ∀ y, y ∈ Fs ↔ y ∈ Fx := fun y ↦ Set.Finite.mem_toFinset _
    have hξy : ∀ y ∈ Fs, ξ y = x := fun y hy ↦ ((hFs y).mp hy).2.2
    have hOU : IsOpen (⋃ y ∈ Fs, O y) := isOpen_biUnion fun y hy ↦ hOo y ((hFs y).mp hy)
    have htube := anr_box_tube T hTc ξ a R r hsph x hx' _ hOU fun z hz hzR hzx ↦
      mem_biUnion ((hFs z).mpr ⟨hz, hzR, hzx⟩) (hyO z ⟨hz, hzR, hzx⟩)
    set W := Metric.ball (ξ a) r ∩ (⋂ y ∈ Fs, Metric.ball x (ρ y)) ∩
      interior {v | ∀ z ∈ T, ‖z - a‖ < R → ξ z = v → z ∈ ⋃ y ∈ Fs, O y}
    have hWo : IsOpen W := (Metric.isOpen_ball.inter (isOpen_biInter_finset fun y _ ↦
      Metric.isOpen_ball)).inter isOpen_interior
    have hWball : ∀ v ∈ W, ∀ y ∈ Fs, v ∈ Metric.ball (ξ y) (ρ y) := by
      intro v hv y hy
      rw [hξy y hy]
      exact mem_iInter₂.mp hv.1.2 y hy
    refine ⟨W, hWo, ⟨⟨hx, mem_iInter₂.mpr fun y hy ↦ Metric.mem_ball_self
      (hρ y ((hFs y).mp hy))⟩, mem_interior_iff_mem_nhds.mpr htube⟩,
      fun v hv ↦ hv.1.1, fun v ↦ ∏ y ∈ Fs, δ y v, ?_, ?_, ?_⟩
    · intro v hv
      exact Finset.analyticAt_fun_prod _ fun y hy ↦ hδ y ((hFs y).mp hy) v (hWball v hv y hy)
    · intro v hv hev
      have hfr := adim9_frequently_ne_zero_finset Fs (fun y ↦ Metric.ball (ξ y) (ρ y))
        (fun y _ ↦ Metric.isOpen_ball) δ
        (fun y hy ↦ (hδ y ((hFs y).mp hy)).continuousOn)
        (fun y hy ↦ hnz y ((hFs y).mp hy)) v (hWball v hv)
      obtain ⟨u, hu, hu0⟩ := (hfr.and_eventually hev).exists
      exact (Finset.prod_ne_zero_iff.mpr fun y hy ↦ (hu y hy).2) hu0
    · rintro v ⟨⟨z, ⟨hzT, hzR, -⟩, rfl⟩, hv⟩
      have hzO := interior_subset hv.2 z hzT hzR rfl
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hzO
      exact Finset.prod_eq_zero hy (hvan y ((hFs y).mp hy) z ⟨hzT, hzy⟩)
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨hx, hxA⟩
    have hx' : ‖x - ξ a‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have htube := anr_box_tube T hTc ξ a R r hsph x hx' ∅ isOpen_empty fun z hz hzR hzx ↦
      hxA ⟨z, ⟨hz, hzR, by rwa [hzx]⟩, hzx⟩
    filter_upwards [htube, Metric.isOpen_ball.mem_nhds hx] with v hv hvb
    refine ⟨hvb, ?_⟩
    rintro ⟨z, ⟨hzT, hzR, -⟩, rfl⟩
    exact hv z hzT hzR rfl

/-! ### Local sheets over the base off the projected exceptional set -/

/-- Finite parameters along a linear map at a point isolated in its fibre, in the form used by
the local sheet construction. -/
theorem anr_finpar (N d : ℕ) (C : Set (Fin (N + 1) → ℂ)) (y : Fin (N + 1) → ℂ) (hy : y ∈ C)
    (U : Set (Fin (N + 1) → ℂ)) (hU : IsOpen U) (hyU : y ∈ U) (m : ℕ)
    (f : Fin m → (Fin (N + 1) → ℂ) → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hUC : ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y' in 𝓝 y, y' ∈ C → L y' = L y → y' = y) :
    ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (N + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (N + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b := by
  intro Q hQ
  have hfin := adim9_local_finite_all N d C y hy U hU hyU m f hf hUC L hiso Q hQ
  refine ⟨_, hfin, fun a h _ ha b hb ↦ ?_⟩
  have hb' : Germ.ofFun (fun z ↦ h (L z)) = b.val := by simpa [map_add] using hb
  change Ideal.Quotient.mk Q (adim9_pb L a) = Ideal.Quotient.mk Q b
  rw [show adim9_pb L a = b from Subtype.ext ((adim9_pb_rep L a h ha).symm.trans hb')]

/-- Over a neighbourhood of a parameter whose whole fibre in the box consists of points of a
pure set, the fibres are enumerated by finitely many analytic sheets off a nowhere locally zero
hypersurface. -/
theorem anr_good_base (N d : ℕ) (B K : Set (Fin (N + 1) → ℂ)) (hKc : IsClosed K)
    (hBK : B ⊆ K)
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (a : Fin (N + 1) → ℂ) (R r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖)
    (G : Set (Fin (d + 1) → ℂ)) (hGo : IsOpen G) (hGball : G ⊆ Metric.ball (ξ a) r)
    (hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z ∈ G → z ∈ B)
    (w : Fin (d + 1) → ℂ) (hw : w ∈ G) :
    ∃ (U : Set (Fin (d + 1) → ℂ)) (δ : (Fin (d + 1) → ℂ) → ℂ) (M : ℕ),
      IsOpen U ∧ w ∈ U ∧ U ⊆ G ∧ AnalyticOnNhd ℂ δ U ∧
      (∀ v ∈ U, ¬ (δ =ᶠ[𝓝 v] fun _ ↦ 0)) ∧
      ∀ v ∈ U, δ v ≠ 0 → ∃ k, k ≤ M ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
        IsOpen W ∧ v ∈ W ∧ W ⊆ U ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
        ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧
          ∀ z, (z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = v') ↔ ∃ j, r' j v' = z := by
  classical
  have hw' : ‖w - ξ a‖ < r := by
    have := hGball hw
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hballR : IsOpen {z : Fin (N + 1) → ℂ | ‖z - a‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  set Fw := {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w}
  have hFw : Fw = {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} := by
    ext z
    constructor
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hBK hz, hzR, hzw⟩
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hKB z hz hzR (hzw ▸ hw), hzR, hzw⟩
  have hFwc : IsCompact Fw := by
    rw [hFw]; exact anr_box_fibre_compact K hKc ξ a R r hsph w hw'
  have hFwf : Fw.Finite := adim9_compact_analytic_finite (N + 1) Fw hFwc fun z hz ↦
    anr_fibre_loc B z (hBloc z hz.1) ξ w a R hz.2.1
  have hiso : ∀ y ∈ Fw, ∀ᶠ y' in 𝓝 y, y' ∈ B → ξ y' = ξ y → y' = y := by
    intro y hy
    have hcl : IsClosed (Fw \ {y}) := (hFwf.subset sdiff_subset).isClosed
    filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl),
      hballR.mem_nhds hy.2.1] with y' hy' hy'R hy'B hξ
    by_contra hne
    exact hy' ⟨⟨hy'B, hy'R, hξ.trans hy.2.2⟩, hne⟩
  obtain ⟨Us, hUs, hdisj⟩ := hFwf.t2_separation
  have hdata : ∀ y ∈ Fw, ∃ (O : Set (Fin (N + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K' : ℕ), IsOpen O ∧ y ∈ O ∧
      O ⊆ Us y ∩ {z | ‖z - a‖ < R} ∧ IsOpen V ∧
      ξ y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K' ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ B ∧ z ∈ O ∧ ξ z = v) ↔ ∃ j, r j v = z := by
    intro y hy
    obtain ⟨U, hU, hyU, m, f, hf, hUB⟩ := hBloc y hy.1
    exact adim9_local_sheets_at N d B ξ y hy.1 ⟨U, hU, hyU, m, f, hf, hUB⟩ (hpure y hy.1)
      (anr_finpar N d B y hy.1 U hU hyU m f hf hUB ξ (hiso y hy)) _
      (((hUs y).2.inter hballR).mem_nhds ⟨(hUs y).1, hy.2.1⟩)
  choose! O V δ K' hOo hyO hOU hVo hyV hδ hnz hsh using hdata
  set Fs := hFwf.toFinset
  have hFs : ∀ y, y ∈ Fs ↔ y ∈ Fw := fun y ↦ Set.Finite.mem_toFinset _
  have hOUn : IsOpen (⋃ y ∈ Fs, O y) := isOpen_biUnion fun y hy ↦ hOo y ((hFs y).mp hy)
  have htube := anr_box_tube K hKc ξ a R r hsph w hw' _ hOUn fun z hz hzR hzw ↦ by
    have hzF : z ∈ Fw := ⟨hKB z hz hzR (hzw ▸ hw), hzR, hzw⟩
    exact mem_biUnion ((hFs z).mpr hzF) (hyO z hzF)
  set U := G ∩ (⋂ y ∈ Fs, V y) ∩
    interior {v | ∀ z ∈ K, ‖z - a‖ < R → ξ z = v → z ∈ ⋃ y ∈ Fs, O y}
  have hUo : IsOpen U := (hGo.inter (isOpen_biInter_finset fun y hy ↦
    hVo y ((hFs y).mp hy))).inter isOpen_interior
  have hUV : ∀ v ∈ U, ∀ y ∈ Fs, v ∈ V y := fun v hv y hy ↦ mem_iInter₂.mp hv.1.2 y hy
  have hcover : ∀ v ∈ U, ∀ z, z ∈ B → ‖z - a‖ < R → ξ z = v → ∃ y ∈ Fs, z ∈ O y := by
    intro v hv z hz hzR hzv
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (interior_subset hv.2 z (hBK hz) hzR hzv)
    exact ⟨y, hy, hzy⟩
  have hwU : w ∈ U := by
    refine ⟨⟨hw, mem_iInter₂.mpr fun y hy ↦ ?_⟩, mem_interior_iff_mem_nhds.mpr htube⟩
    have := hyV y ((hFs y).mp hy)
    rwa [((hFs y).mp hy).2.2] at this
  refine ⟨U, fun v ↦ ∏ y ∈ Fs, δ y v, ∑ y ∈ Fs, K' y, hUo, hwU, fun v hv ↦ hv.1.1,
    fun v hv ↦ Finset.analyticAt_fun_prod _ fun y hy ↦
      hδ y ((hFs y).mp hy) v (hUV v hv y hy), ?_, ?_⟩
  · intro v hv hev
    have hfr := adim9_frequently_ne_zero_finset Fs V (fun y hy ↦ hVo y ((hFs y).mp hy)) δ
      (fun y hy ↦ (hδ y ((hFs y).mp hy)).continuousOn)
      (fun y hy ↦ hnz y ((hFs y).mp hy)) v fun y hy ↦ hUV v hv y hy
    obtain ⟨u, hu, hu0⟩ := (hfr.and_eventually hev).exists
    exact (Finset.prod_ne_zero_iff.mpr fun y hy ↦ (hu y hy).2) hu0
  · intro v hv hδv
    have hδy : ∀ y ∈ Fs, δ y v ≠ 0 := fun y hy ↦ Finset.prod_ne_zero_iff.mp hδv y hy
    choose! k hkK W r hWo hvW hra hr using fun y (hy : y ∈ Fs) ↦
      hsh y ((hFs y).mp hy) v (hUV v hv y hy) (hδy y hy)
    let σ := Σ y : Fs, Fin (k y)
    let e := Fintype.equivFin σ
    let R' : Fin (Fintype.card σ) → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ) := fun j ↦
      r (e.symm j).1 (e.symm j).2
    set W' := U ∩ ⋂ y ∈ Fs, W y
    have hW'o : IsOpen W' := hUo.inter (isOpen_biInter_finset fun y hy ↦ hWo y hy)
    have hW'W : ∀ v' ∈ W', ∀ y ∈ Fs, v' ∈ W y := fun v' hv' y hy ↦ mem_iInter₂.mp hv'.2 y hy
    refine ⟨Fintype.card σ, ?_, W', R', hW'o, ⟨hv, mem_iInter₂.mpr fun y hy ↦ hvW y hy⟩,
      inter_subset_left, fun j ↦ ?_, fun v' hv' ↦ ⟨?_, fun z ↦ ?_⟩⟩
    · rw [Fintype.card_sigma, ← Finset.sum_coe_sort Fs K']
      exact Finset.sum_le_sum fun y _ ↦ by simpa using hkK y y.2
    · exact (hra _ (e.symm j).1.2 _).mono fun v' hv' ↦ hW'W v' hv' _ (e.symm j).1.2
    · have key : ∀ a b : σ, r a.1 a.2 v' = r b.1 b.2 v' → a = b := by
        rintro ⟨y₁, j₁⟩ ⟨y₂, j₂⟩ h
        have hz₁ := ((hr y₁ y₁.2 v' (hW'W v' hv' _ y₁.2)).2 _).mpr ⟨j₁, rfl⟩
        have hz₂ := ((hr y₂ y₂.2 v' (hW'W v' hv' _ y₂.2)).2 _).mpr ⟨j₂, h.symm⟩
        have hy : y₁ = y₂ := by
          by_contra hne
          have hne' : y₁.val ≠ y₂.val := fun h ↦ hne (Subtype.ext h)
          have hd := hdisj ((hFs _).mp y₁.2) ((hFs _).mp y₂.2) hne'
          exact Set.disjoint_left.mp hd (hOU _ ((hFs _).mp y₁.2) hz₁.2.1).1
            (hOU _ ((hFs _).mp y₂.2) hz₂.2.1).1
        subst hy
        have := (hr y₁ y₁.2 v' (hW'W v' hv' _ y₁.2)).1 h
        simp only at this
        subst this
        rfl
      intro i j hij
      exact e.symm.injective (key _ _ hij)
    · constructor
      · rintro ⟨hzB, hzR, hzv⟩
        obtain ⟨y, hy, hzy⟩ := hcover v' hv'.1 z hzB hzR hzv
        obtain ⟨j, hj⟩ := ((hr y hy v' (hW'W v' hv' y hy)).2 z).mp ⟨hzB, hzy, hzv⟩
        refine ⟨e ⟨⟨y, hy⟩, j⟩, ?_⟩
        change (fun x : σ ↦ r x.1 x.2 v') (e.symm (e _)) = z
        rw [e.symm_apply_apply]
        exact hj
      · rintro ⟨j, rfl⟩
        obtain ⟨hzB, hzO, hzv⟩ := ((hr _ (e.symm j).1.2 v'
          (hW'W v' hv' _ (e.symm j).1.2)).2 _).mpr ⟨(e.symm j).2, rfl⟩
        exact ⟨hzB, (hOU _ ((hFs _).mp (e.symm j).1.2) hzO).2, hzv⟩

/-- No neighbourhood of a point of a pure set that is isolated in its fibre lies over a
hypersurface that is not locally zero at its parameter. -/
theorem anr_thin_at (N d : ℕ) (B : Set (Fin (N + 1) → ℂ)) (y : Fin (N + 1) → ℂ) (hy : y ∈ B)
    (hBloc : ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y' in 𝓝 y, y' ∈ B → ξ y' = ξ y → y' = y)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hyV : ξ y ∈ V)
    (h : (Fin (d + 1) → ℂ) → ℂ) (hh : AnalyticAt ℂ h (ξ y))
    (hnz : ¬ (h =ᶠ[𝓝 (ξ y)] fun _ ↦ 0)) :
    y ∈ closure (B ∩ ξ ⁻¹' {w | w ∈ V ∧ h w ≠ 0}) := by
  obtain ⟨U, hU, hyU, m, f, hf, hUB⟩ := hBloc
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes (adim9b_germ_ideal_ne_top (N + 1) B y hy)
  have : Q.IsPrime := hQ.1.1
  obtain ⟨θ, hθ, hcomp⟩ := anr_finpar N d B y hy U hU hyU m f hf hUB ξ hiso Q hQ
  have hinj := adim9_injective_of_finite_of_dim d θ hθ (hpure Q hQ)
  refine adim9_thin_of_injective_parameters N d B ξ y Q hQ θ hinj (fun a h' ha' hra b hb ↦
    hcomp a h' ha' hra b ?_) V hV hyV h hh hnz
  simpa [map_add] using hb

/-- A point of the closure of a set lying in an open set is in the closure of the part of the
set inside the open set. -/
theorem anr_mem_closure_inter_open {X : Type*} [TopologicalSpace X] {S O : Set X} {y : X}
    (hy : y ∈ closure S) (hO : IsOpen O) (hyO : y ∈ O) : y ∈ closure (S ∩ O) := by
  rw [mem_closure_iff_frequently] at hy ⊢
  exact (hy.and_eventually (hO.mem_nhds hyO)).mono fun z hz ↦ hz

/-- Fibres in the box over a parameter whose fibre avoids the exceptional set are finite. -/
theorem anr_fib_finite {n p : ℕ} (B K : Set (Fin n → ℂ)) (hKc : IsClosed K) (hBK : B ⊆ K)
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (a : Fin n → ℂ) (R r : ℝ)
    (hsph : ∀ z ∈ K, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖) (w : Fin p → ℂ) (hw : ‖w - ξ a‖ < r)
    (hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z = w → z ∈ B) :
    {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w}.Finite := by
  have hFw : {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w} = {z | z ∈ K ∧ ‖z - a‖ < R ∧ ξ z = w} := by
    ext z
    constructor
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hBK hz, hzR, hzw⟩
    · rintro ⟨hz, hzR, hzw⟩
      exact ⟨hKB z hz hzR hzw, hzR, hzw⟩
  have hc : IsCompact {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = w} := by
    rw [hFw]; exact anr_box_fibre_compact K hKc ξ a R r hsph w hw
  exact adim9_compact_analytic_finite n _ hc fun z hz ↦
    anr_fibre_loc B z (hBloc z hz.1) ξ w a R hz.2.1

/-- A point of a finite fibre in the box is isolated in its fibre. -/
theorem anr_fib_iso {n p : ℕ} (B : Set (Fin n → ℂ)) (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (a : Fin n → ℂ) (R : ℝ) (y : Fin n → ℂ) (hyR : ‖y - a‖ < R)
    (hfin : {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = ξ y}.Finite) :
    ∀ᶠ y' in 𝓝 y, y' ∈ B → ξ y' = ξ y → y' = y := by
  have hballR : IsOpen {z : Fin n → ℂ | ‖z - a‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have hcl : IsClosed ({z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = ξ y} \ {y}) :=
    (hfin.subset sdiff_subset).isClosed
  filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl), hballR.mem_nhds hyR]
    with y' hy' hy'R hy'B hξ
  by_contra hne
  exact hy' ⟨⟨hy'B, hy'R, hξ⟩, hne⟩

/-! ### Equations on the box -/

/-- On a box over which the projection is proper, and given a dense set of points of the pure
set isolated in their fibres, the closure of the pure set is cut out by finitely many analytic
equations: monic polynomials in moment observables whose coefficients are the bounded
symmetric functions of the sheets, continued across the projected exceptional set. -/
theorem anr_box_equations (N d : ℕ) (T B : Set (Fin (N + 1) → ℂ)) (hTc : IsClosed T)
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hclB : closure B ⊆ B ∪ T)
    (ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (a : Fin (N + 1) → ℂ) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hsph : ∀ z ∈ closure B ∪ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖)
    (DB : Set (Fin (N + 1) → ℂ)) (hDB : DB ⊆ B) (hDBd : B ⊆ closure DB)
    (hDBiso : ∀ y ∈ DB, ∀ᶠ z in 𝓝 y, z ∈ B → ξ z = ξ y → z = y) :
    ∃ (m : ℕ) (f : Fin m → (Fin (N + 1) → ℂ) → ℂ),
      (∀ j, AnalyticOnNhd ℂ (f j) {z | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}) ∧
      ∀ z ∈ {z | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}, (z ∈ closure B ↔ ∀ j, f j z = 0) := by
  classical
  set K := closure B ∪ T
  have hKc : IsClosed K := isClosed_closure.union hTc
  have hBK : B ⊆ K := subset_closure.trans subset_union_left
  set V' := Metric.ball (ξ a) r
  set A' := ξ '' {z | z ∈ T ∧ ‖z - a‖ < R ∧ ‖ξ z - ξ a‖ < r}
  obtain ⟨hA'thin, hGo⟩ := anr_image_thin N d T hTc hTloc hdimT ξ a R r
    (fun z hz ↦ hsph z (Or.inr hz))
  set G := V' \ A'
  have hmemV : ∀ v, v ∈ V' ↔ ‖v - ξ a‖ < r := fun v ↦ by
    rw [Metric.mem_ball, dist_eq_norm]
  have hKB : ∀ z ∈ K, ‖z - a‖ < R → ξ z ∈ G → z ∈ B := by
    intro z hz hzR hzG
    have hzr : ‖ξ z - ξ a‖ < r := (hmemV _).mp hzG.1
    rcases hz with hz | hz
    · rcases hclB hz with h | h
      · exact h
      · exact absurd ⟨z, ⟨h, hzR, hzr⟩, rfl⟩ hzG.2
    · exact absurd ⟨z, ⟨hz, hzR, hzr⟩, rfl⟩ hzG.2
  set fib : (Fin (d + 1) → ℂ) → Set (Fin (N + 1) → ℂ) := fun v ↦
    {z | z ∈ B ∧ ‖z - a‖ < R ∧ ξ z = v}
  have hfibfin : ∀ v ∈ G, (fib v).Finite := fun v hv ↦
    anr_fib_finite B K hKc hBK hBloc ξ a R r hsph v ((hmemV v).mp hv.1)
      fun z hz hzR hzv ↦ hKB z hz hzR (hzv ▸ hv)
  -- good parameters and the bad set
  let Good : (Fin (d + 1) → ℂ) → Prop := fun v ↦ ∃ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
    (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
    IsOpen W ∧ v ∈ W ∧ W ⊆ G ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
    ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧ ∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z
  set E := {v | v ∈ G ∧ ¬ Good v}
  have hEthin : ∀ x ∈ G, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ G ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0} := by
    intro x hx
    obtain ⟨U, δ, M, hUo, hxU, hUG, hδ, hnz, hsh⟩ := anr_good_base N d B K hKc hBK hBloc
      hpure ξ a R r hsph G hGo sdiff_subset hKB x hx
    refine ⟨U, hUo, hxU, hUG, δ, hδ, hnz, ?_⟩
    rintro v ⟨⟨-, hvgood⟩, hvU⟩
    by_contra hδv
    obtain ⟨k, -, W, r', hWo, hvW, hWU, hra, hr⟩ := hsh v hvU hδv
    exact hvgood ⟨k, W, r', hWo, hvW, hWU.trans hUG, hra, hr⟩
  set D := G \ E
  have hDG : ∀ v ∈ D, Good v := by
    rintro v ⟨hvG, hvE⟩
    by_contra h
    exact hvE ⟨hvG, h⟩
  have hGoodW : ∀ v, Good v → ∃ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
      (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
      IsOpen W ∧ v ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
      ∀ v' ∈ W, Function.Injective (fun j ↦ r' j v') ∧ ∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z := by
    rintro v ⟨k, W, r', hWo, hvW, hWG, hra, hr⟩
    refine ⟨k, W, r', hWo, hvW, fun v' hv' ↦ ⟨hWG hv', fun hE ↦ hE.2 ?_⟩, hra, hr⟩
    exact ⟨k, W, r', hWo, hv', hWG, hra, hr⟩
  have hDo : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    obtain ⟨k, W, r', hWo, hvW, hWD, -, -⟩ := hGoodW v (hDG v hv)
    exact Filter.mem_of_superset (hWo.mem_nhds hvW) hWD
  have hDconn : IsPreconnected D :=
    anr_thin2_preconnected V' A' E (convex_ball _ _).isPreconnected hA'thin hEthin hDo
  have hDdense : V' ⊆ closure D := anr_thin2_dense V' A' E hA'thin hEthin
  -- the sheet count is constant on the good set
  set sf : (Fin (d + 1) → ℂ) → Finset (Fin (N + 1) → ℂ) := fun v ↦
    if h : (fib v).Finite then h.toFinset else ∅
  have hsf : ∀ v, (fib v).Finite → ∀ z, z ∈ sf v ↔ z ∈ fib v := by
    intro v hv z
    simp only [sf, hv, ↓reduceDIte, Set.Finite.mem_toFinset]
  have hsheetfin : ∀ (k : ℕ) (r' : Fin k → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)) v',
      (∀ z, z ∈ fib v' ↔ ∃ j, r' j v' = z) → (fib v').Finite := by
    intro k r' v' h
    refine (Set.finite_range fun j ↦ r' j v').subset fun z hz ↦ ?_
    obtain ⟨j, hj⟩ := (h z).mp hz
    exact ⟨j, hj⟩
  have hcardloc : ∀ v ∈ D, ∃ k : ℕ, ∀ᶠ v' in 𝓝 v, (sf v').card = k := by
    intro v hv
    obtain ⟨k, W, r', hWo, hvW, -, -, hr⟩ := hGoodW v (hDG v hv)
    refine ⟨k, Filter.mem_of_superset (hWo.mem_nhds hvW) fun v' hv' ↦ ?_⟩
    have hfin := hsheetfin k r' v' (hr v' hv').2
    exact adim9_fibre_card_of_sheets sf r' v'
      ⟨(hr v' hv').1, fun z ↦ (hsf v' hfin z).trans ((hr v' hv').2 z)⟩
  obtain ⟨v₀, hv₀⟩ : D.Nonempty := by
    have h := hDdense (Metric.mem_ball_self hr)
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h
    exact h
  set M := (sf v₀).card
  have hcardM : ∀ v ∈ D, (sf v).card = M := by
    intro v hv
    have hcont : ContinuousOn (fun v ↦ (sf v).card) D := by
      intro x hx
      obtain ⟨k, hk⟩ := hcardloc x hx
      exact (continuousAt_const.congr (hk.mono fun v hv ↦ hv.symm)).continuousWithinAt
    exact hDconn.constant_of_mapsTo (T := univ)
      (isDiscrete_iff_discreteTopology.mpr inferInstance) hcont (mapsTo_univ _ _) hv hv₀
  have hsheetsM : ∀ x ∈ D, ∃ (W : Set (Fin (d + 1) → ℂ))
      (r' : Fin M → (Fin (d + 1) → ℂ) → (Fin (N + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r' j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r' j y) ∧
        ∀ z, z ∈ sf y ↔ ∃ j, r' j y = z := by
    intro x hx
    obtain ⟨k, W, r', hWo, hxW, hWD, hra, hr⟩ := hGoodW x (hDG x hx)
    have hr' : ∀ y ∈ W, Function.Injective (fun j ↦ r' j y) ∧
        ∀ z, z ∈ sf y ↔ ∃ j, r' j y = z := fun y hy ↦
      ⟨(hr y hy).1, fun z ↦ (hsf y (hsheetfin k r' y (hr y hy).2) z).trans ((hr y hy).2 z)⟩
    have hk : k = M := by
      rw [← hcardM x hx, adim9_fibre_card_of_sheets sf r' x (hr' x hxW)]
    subst hk
    exact ⟨W, r', hWo, hxW, hWD, hra, hr'⟩
  -- bounded symmetric coefficients, continued to the base ball
  have hbnd : ∀ x ∈ D, ∀ z ∈ sf x, ‖z‖ ≤ ‖a‖ + R := by
    intro x hx z hz
    have hz' := (hsf x (hfibfin x hx.1) z).mp hz
    calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
      _ ≤ ‖a‖ + R := by linarith [hz'.2.1]
  have hcoefs : ∀ obs : (Fin (N + 1) → ℂ) →L[ℂ] ℂ, ∃ b : Fin M → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) V') ∧ ∀ w ∈ D, ∀ t : ℂ,
        (adim9_fibrePolynomial (N + 1) (sf w) obs).eval t =
          t ^ M + ∑ i : Fin M, b i w * t ^ (i : ℕ) := by
    intro obs
    have hRb : 0 ≤ ‖obs‖ * (‖a‖ + R) := by positivity
    have hobs : ∀ x ∈ D, ∀ z ∈ sf x, ‖obs z‖ ≤ ‖obs‖ * (‖a‖ + R) := fun x hx z hz ↦
      (obs.le_opNorm z).trans (mul_le_mul_of_nonneg_left (hbnd x hx z hz) (norm_nonneg _))
    obtain ⟨hcoef, hmon⟩ := adim9_sheet_coefficients_aux (N + 1) (d + 1) M D sf hsheetsM obs
      _ hRb hobs
    have hext : ∀ i : Fin M, ∃ b : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ b V' ∧
        EqOn b (fun w ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i) D := by
      intro i
      obtain ⟨F, hF, hFf, -⟩ := anr_thin2_extension V' A' E hA'thin hEthin
        (fun w ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i) (hcoef i) _
        (fun x hx ↦ (hmon x hx).2.2.1 i)
      exact ⟨F, hF, hFf⟩
    choose b hb hbeq using hext
    refine ⟨b, hb, fun w hw t ↦ ?_⟩
    obtain ⟨hm, hdeg, -, -⟩ := hmon w hw
    conv_lhs => rw [hm.as_sum, hdeg]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_range (fun i ↦ (adim9_fibrePolynomial (N + 1) (sf w) obs).coeff i *
      t ^ i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hbeq i hw]
  -- moment observables and the equations
  let ℓ : Fin (N * M + 1) → (Fin (N + 1) → ℂ) →L[ℂ] ℂ := fun t ↦
    ∑ i : Fin (N + 1), (((t : ℕ) : ℂ) ^ (i : ℕ)) •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) ↦ ℂ) i
  have hℓ : ∀ t z, ℓ t z = ∑ i : Fin (N + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * z i := by
    intro t z
    simp [ℓ, sum_apply]
  choose b hb heq using fun t ↦ hcoefs (ℓ t)
  let f : Fin (N * M + 1) → (Fin (N + 1) → ℂ) → ℂ := fun t z ↦
    ℓ t z ^ M + ∑ i : Fin M, b t i (ξ z) * ℓ t z ^ (i : ℕ)
  set Box := {z : Fin (N + 1) → ℂ | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R}
  have hBoxo : IsOpen Box :=
    (isOpen_lt (ξ.continuous.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hBoxV : ∀ z ∈ Box, ξ z ∈ V' := fun z hz ↦ (hmemV _).mpr hz.1
  have hfa : ∀ t, AnalyticOnNhd ℂ (f t) Box := by
    intro t z hz
    have hℓa : AnalyticAt ℂ (ℓ t) z := (ℓ t).analyticAt z
    refine (hℓa.pow M).add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
    exact ((hb t i (ξ z) (hBoxV z hz)).comp (ξ.analyticAt z)).mul (hℓa.pow _)
  set Gs := B ∩ Box ∩ ξ ⁻¹' D
  have hfG : ∀ t, ∀ y ∈ Gs, f t y = 0 := by
    intro t y hy
    have h := heq t (ξ y) hy.2 (ℓ t y)
    simp only [f, ← h, adim9_fibrePolynomial, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_eq_zero (i := y) ?_ (sub_self _)
    exact (hsf (ξ y) (hfibfin (ξ y) hy.2.1) y).mpr ⟨hy.1.1, hy.1.2.2, rfl⟩
  -- density of the good part
  have hstepG : ∀ y ∈ B, y ∈ Box → ξ y ∈ G → y ∈ closure Gs := by
    intro y hyB hyBox hyG
    obtain ⟨W, hWo, hyW, hWG, δ, hδ, hnz, hEW⟩ := hEthin (ξ y) hyG
    have hiso := anr_fib_iso B ξ a R y hyBox.2 (hfibfin (ξ y) hyG)
    have h1 := anr_thin_at N d B y hyB (hBloc y hyB) (hpure y hyB) ξ hiso W hWo hyW δ
      (hδ _ hyW) (hnz _ hyW)
    refine closure_mono ?_ (anr_mem_closure_inter_open h1 hBoxo hyBox)
    rintro z ⟨⟨hzB, hzW, hδz⟩, hzBox⟩
    exact ⟨⟨hzB, hzBox⟩, hWG hzW, fun hzE ↦ hδz (hEW ⟨hzE, hzW⟩)⟩
  have hstepDB : ∀ y ∈ DB, y ∈ Box → y ∈ closure Gs := by
    intro y hyD hyBox
    have hyB := hDB hyD
    obtain ⟨W, hWo, hyW, hWV, δ, hδ, hnz, hAW⟩ := hA'thin (ξ y) (hBoxV y hyBox)
    have h1 := anr_thin_at N d B y hyB (hBloc y hyB) (hpure y hyB) ξ (hDBiso y hyD) W hWo
      hyW δ (hδ _ hyW) (hnz _ hyW)
    have h2 := anr_mem_closure_inter_open h1 hBoxo hyBox
    rw [← closure_closure (s := Gs)]
    refine closure_mono ?_ h2
    rintro z ⟨⟨hzB, hzW, hδz⟩, hzBox⟩
    exact hstepG z hzB hzBox ⟨hWV hzW, fun hzA ↦ hδz (hAW ⟨hzA, hzW⟩)⟩
  have hdense : ∀ z ∈ closure B, z ∈ Box → z ∈ closure Gs := by
    intro z hz hzBox
    have h1 : closure (B ∩ Box) ⊆ closure Gs := by
      rw [← closure_closure (s := Gs)]
      refine closure_mono fun y hy ↦ ?_
      have hy' := anr_mem_closure_inter_open (hDBd hy.1) hBoxo hy.2
      rw [← closure_closure (s := Gs)]
      exact closure_mono (fun x hx ↦ hstepDB x hx.1 hx.2) hy'
    exact h1 (anr_mem_closure_inter_open hz hBoxo hzBox)
  have hfwd : ∀ t, ∀ z ∈ Box, z ∈ closure Gs → f t z = 0 := by
    intro t z hz hzG
    exact ((hfa t z hz).continuousAt.continuousWithinAt).eq_const_of_mem_closure hzG (hfG t)
  -- the converse, by limits of whole fibres over good parameters
  have hbwd : ∀ z ∈ Box, (∀ t, f t z = 0) → z ∈ closure B := by
    intro z hz hf0
    obtain ⟨ws, hwsD, hws⟩ := mem_closure_iff_seq_limit.mp (hDdense (hBoxV z hz))
    let Ep : ℕ → Fin M → Fin (N + 1) → ℂ := fun m j ↦
      ((sf (ws m)).equivFin.symm (Fin.cast (hcardM _ (hwsD m)).symm j) : _)
    have hEmem : ∀ m j, Ep m j ∈ sf (ws m) := fun m j ↦ Finset.coe_mem _
    have hEimg : ∀ m, sf (ws m) = Finset.univ.image (Ep m) := by
      intro m
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hy
        refine ⟨Fin.cast (hcardM _ (hwsD m)) ((sf (ws m)).equivFin ⟨y, hy⟩), ?_⟩
        simp [Ep]
      · rintro ⟨j, rfl⟩
        exact hEmem m j
    have hEinj : ∀ m, Function.Injective (Ep m) := by
      intro m i j hij
      have := Subtype.ext hij
      simpa using (sf (ws m)).equivFin.symm.injective this
    have hEB : ∀ m j, Ep m j ∈ B ∧ ‖Ep m j‖ ≤ ‖a‖ + R := fun m j ↦
      ⟨((hsf _ (hfibfin _ (hwsD m).1) _).mp (hEmem m j)).1, hbnd _ (hwsD m) _ (hEmem m j)⟩
    have hEb : ∀ m, Ep m ∈ Metric.closedBall (0 : Fin M → Fin (N + 1) → ℂ) (‖a‖ + R) := by
      intro m
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ (hEB m j).2
    obtain ⟨Y, -, φ, hφ, hY⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hEb
    have hYj : ∀ j, Tendsto (fun m ↦ Ep (φ m) j) atTop (𝓝 (Y j)) :=
      fun j ↦ ((continuous_apply j).tendsto Y).comp hY
    have hYmem : ∀ j, Y j ∈ closure B := fun j ↦
      isClosed_closure.mem_of_tendsto (hYj j)
        (Eventually.of_forall fun m ↦ subset_closure (hEB (φ m) j).1)
    have hwφ : Tendsto (fun m ↦ ws (φ m)) atTop (𝓝 (ξ z)) := hws.comp hφ.tendsto_atTop
    have hroot : ∀ t, ∃ j, ℓ t z = ℓ t (Y j) := by
      intro t
      set x := ℓ t z
      have hlhs : Tendsto (fun m ↦ x ^ M + ∑ i : Fin M, b t i (ws (φ m)) * x ^ (i : ℕ))
          atTop (𝓝 (f t z)) := by
        refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ ↦ ?_)
        exact (((hb t i (ξ z) (hBoxV z hz)).continuousAt.tendsto).comp hwφ).mul
          tendsto_const_nhds
      have hrhs : Tendsto (fun m ↦ ∏ j, (x - ℓ t (Ep (φ m) j))) atTop
          (𝓝 (∏ j, (x - ℓ t (Y j)))) :=
        tendsto_finsetProd _ fun j _ ↦
          tendsto_const_nhds.sub (((ℓ t).continuous.tendsto _).comp (hYj j))
      have hEq : ∀ m, x ^ M + ∑ i : Fin M, b t i (ws (φ m)) * x ^ (i : ℕ) =
          ∏ j, (x - ℓ t (Ep (φ m) j)) := by
        intro m
        rw [← heq t (ws (φ m)) (hwsD (φ m)) x, hEimg, adim9_fibrePolynomial,
          Finset.prod_image fun a _ b _ h ↦ hEinj (φ m) h]
        simp [eval_prod]
      have hlim := tendsto_nhds_unique (hlhs.congr hEq) hrhs
      rw [hf0 t] at hlim
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hlim.symm
      exact ⟨j, sub_eq_zero.mp hj⟩
    obtain ⟨j, hj⟩ := adim9_moment_observables_separate N M z Y fun t ↦ by
      obtain ⟨j, hj⟩ := hroot t
      exact ⟨j, by rw [← hℓ, ← hℓ, hj]⟩
    exact hj ▸ hYmem j
  exact ⟨N * M + 1, f, hfa, fun z hz ↦ ⟨fun h t ↦ hfwd t z hz (hdense z h hz),
    hbwd z hz⟩⟩

/-! ### Choice of the projection and of the box -/

/-- A set all of whose points are isolated is countable. -/
theorem anr_countable_of_isolated {n : ℕ} (S : Set (Fin n → ℂ))
    (h : ∀ y ∈ S, ∀ᶠ z in 𝓝 y, z ∈ S → z = y) : S.Countable := by
  have : DiscreteTopology S := discreteTopology_of_noAccPts fun x hx hacc ↦ by
    rw [accPt_iff_frequently] at hacc
    obtain ⟨z, ⟨hzx, hzS⟩, hz⟩ := (hacc.and_eventually (h x hx)).exists
    exact hzx (hz hzS)
  have : Countable S := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact Set.countable_coe_iff.mp this

/-- A projection to `ℂ^(d+1)` whose fibre through `a` meets `T` only at `a` near `a` and meets
the pure set in a countable set, and whose fibres through the points of a countable subset of the
pure set are isolated there. -/
theorem anr_choose_projection (N d : ℕ) (T B : Set (Fin (N + 1) → ℂ))
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hdimB : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (a : Fin (N + 1) → ℂ) (ha : a ∈ T) (DB : Set (Fin (N + 1) → ℂ)) (hDBc : DB.Countable)
    (hDB : DB ⊆ B) :
    ∃ ξ : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ),
      (∀ᶠ z in 𝓝 a, z ∈ T → ξ z = ξ a → z = a) ∧
      (B ∩ {z | ξ z = ξ a}).Countable ∧
      ∀ y ∈ DB, ∀ᶠ z in 𝓝 y, z ∈ B → ξ z = ξ y → z = y := by
  have : Countable DB := hDBc.to_subtype
  let S : Option (Option DB) → Set (Fin (N + 1) → ℂ) := fun i ↦ match i with
    | none => T
    | some _ => B
  let bp : Option (Option DB) → Fin (N + 1) → ℂ := fun i ↦ match i with
    | none => a
    | some none => a
    | some (some y) => y
  let e : Option (Option DB) → ℕ := fun i ↦ match i with
    | none => d
    | some _ => d + 1
  have hloc : ∀ i, ∀ y ∈ S i, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ S i ↔ ∀ j, f j z = 0) := by
    rintro (_ | _) y hy
    · exact hTloc y hy
    · exact hBloc y hy
  have hdim : ∀ i, ∀ y ∈ S i, ∀ Q ∈ (adim2_ideal (N + 1)
      (adim2_germ (N + 1) (S i) y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (e i : WithBot ℕ∞) := by
    rintro (_ | _) y hy
    · exact hdimT y hy
    · exact hdimB y hy
  obtain ⟨ξ, hξ⟩ := anr_slice S bp e hloc hdim (d + 1)
  have hiso : ∀ i, ∀ y ∈ S i ∩ {z | ξ z = ξ (bp i)},
      ∀ᶠ z in 𝓝 y, z ∈ S i ∩ {z | ξ z = ξ (bp i)} → z = y := by
    intro i y hy
    refine anr_isolated_of_dims _ y hy fun Q hQ ↦ ?_
    have := hξ i y hy Q hQ
    have he : e i - (d + 1) = 0 := by rcases i with _ | _ <;> simp [e]
    rw [he] at this
    exact_mod_cast this
  refine ⟨ξ, ?_, ?_, ?_⟩
  · filter_upwards [hiso none a ⟨ha, rfl⟩] with z hz hzT hzξ
    exact hz ⟨hzT, hzξ⟩
  · exact anr_countable_of_isolated _ fun y hy ↦ hiso (some none) y hy
  · intro y hy
    filter_upwards [hiso (some (some ⟨y, hy⟩)) y ⟨hDB hy, rfl⟩] with z hz hzB hzξ
    exact hz ⟨hzB, hzξ⟩

/-- Radii of a box around a point of the exceptional set on which the projection is proper. -/
theorem anr_choose_radii {n p : ℕ} (T B : Set (Fin n → ℂ)) (hTc : IsClosed T)
    (hclB : closure B ⊆ B ∪ T) (ξ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)) (a : Fin n → ℂ)
    (hT : ∀ᶠ z in 𝓝 a, z ∈ T → ξ z = ξ a → z = a) (hB : (B ∩ {z | ξ z = ξ a}).Countable) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ closure B ∪ T, ‖z - a‖ = R → r ≤ ‖ξ z - ξ a‖ := by
  obtain ⟨R₀, hR₀, hball⟩ := Metric.eventually_nhds_iff.mp hT
  set Cn := (fun z ↦ ‖z - a‖) '' (B ∩ {z | ξ z = ξ a})
  have hCn : Cn.Countable := hB.image _
  obtain ⟨R, hR, hRC⟩ : ∃ R ∈ Ioo 0 R₀, R ∉ Cn := by
    by_contra h
    push Not at h
    have h0 := hCn.measure_zero MeasureTheory.volume
    have h1 : MeasureTheory.volume (Ioo 0 R₀) = 0 :=
      MeasureTheory.measure_mono_null (fun x hx ↦ h x hx) h0
    rw [Real.volume_Ioo] at h1
    have : (0 : ℝ) < R₀ - 0 := by linarith
    exact absurd h1 (by simpa using this)
  have hsph : ∀ z ∈ closure B ∪ T, ξ z = ξ a → ‖z - a‖ ≠ R := by
    intro z hz hzξ hzR
    have hzT : z ∈ T → False := fun hzT ↦ by
      have hza := hball (show dist z a < R₀ by rw [dist_eq_norm, hzR]; exact hR.2) hzT hzξ
      rw [hza, sub_self, norm_zero] at hzR
      linarith [hR.1]
    rcases hz with hz | hz
    · rcases hclB hz with h | h
      · exact hRC ⟨z, ⟨h, hzξ⟩, hzR⟩
      · exact hzT h
    · exact hzT hz
  obtain ⟨r, hr, hr'⟩ := anr_box_radius (closure B ∪ T) (isClosed_closure.union hTc) ξ a R hsph
  exact ⟨R, hR.1, r, hr, hr'⟩

/-- Local equations of the closure of the pure set at a point of the exceptional set. -/
theorem anr_rs_local (N d : ℕ) (T B : Set (Fin (N + 1) → ℂ)) (hTc : IsClosed T)
    (hTloc : ∀ y ∈ T, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ T ↔ ∀ j, f j z = 0))
    (hdimT : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞))
    (hBloc : ∀ y ∈ B, ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0))
    (hpure : ∀ y ∈ B, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) B y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hclB : closure B ⊆ B ∪ T) (a : Fin (N + 1) → ℂ) (ha : a ∈ T) :
    ∃ U : Set (Fin (N + 1) → ℂ), IsOpen U ∧ a ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin (N + 1) → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ closure B ↔ ∀ j, f j z = 0) := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense B
  set DB : Set (Fin (N + 1) → ℂ) := Subtype.val '' s
  have hDB : DB ⊆ B := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hDBd : B ⊆ closure DB := by
    intro y hy
    have h1 : (⟨y, hy⟩ : B) ∈ closure s := hsd.closure_eq ▸ mem_univ _
    exact mem_closure_image continuous_subtype_val.continuousAt h1
  obtain ⟨ξ, hξT, hξB, hξD⟩ := anr_choose_projection N d T B hTloc hdimT hBloc
    (fun y hy Q hQ ↦ (hpure y hy Q hQ).le) a ha DB (hsc.image _) hDB
  obtain ⟨R, hR, r, hr, hsph⟩ := anr_choose_radii T B hTc hclB ξ a hξT hξB
  obtain ⟨m, f, hf, hfeq⟩ := anr_box_equations N d T B hTc hTloc hdimT hBloc hpure hclB ξ a R
    r hR hr hsph DB hDB hDBd hξD
  refine ⟨{z | ‖ξ z - ξ a‖ < r ∧ ‖z - a‖ < R},
    (isOpen_lt (ξ.continuous.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const),
    ⟨by simp [hr], by simp [hR]⟩, m, f, hf, hfeq⟩

/-! ### The Remmert–Stein extension theorem -/

/-- Closed analyticity in `ℂⁿ` from local equations at each point. -/
theorem anr_isClosedAnalytic_of_local {n : ℕ} (Z : Set (Fin n → ℂ)) (hZ : IsClosed Z)
    (h : ∀ x ∈ Z, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ Z ↔ ∀ j, f j z = 0)) :
    IsClosedAnalytic (Fin n → ℂ) Z := by
  refine ⟨hZ, fun x hx ↦ ?_⟩
  obtain ⟨U, hU, hxU, m, f, hf, hUZ⟩ := h x hx
  refine ⟨U, hU, ?_, ?_, m, f, hf, ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hxU
  · simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  · intro z hz
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using hUZ z hz

/-- Local equations at each point of a closed analytic subset of `ℂⁿ`. -/
theorem anr_loc_of_isClosedAnalytic {n : ℕ} (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z) :
    ∀ y ∈ Z, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ Z ↔ ∀ j, f j z = 0) := by
  intro y hy
  obtain ⟨U, hU, hyU, -, m, f, hf, hUZ⟩ := hZ.2 y hy
  refine ⟨U, hU, ?_, m, f, hf, fun z hz ↦ ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hyU
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using hUZ z hz

/-- **Remmert–Stein.** Let `T ⊆ ℂⁿ` be closed analytic of dimension `< p` at each of its points,
and `B ⊆ ℂⁿ \ T` closed analytic in `ℂⁿ \ T` and of pure dimension `p`. Then the closure of `B`
is closed analytic in `ℂⁿ`.
Source: Remmert–Stein, Math. Ann. 126 (1953), 263–306, Satz 13; Demailly, Complex Analytic and
Differential Geometry (2012), II, Theorem 8.7 and its proof, step 2. -/
theorem anr_remmert_stein (n p : ℕ) (T B : Set (Fin n → ℂ))
    (hT : IsClosedAnalytic (Fin n → ℂ) T) (hBT : Disjoint B T)
    (hB : ∀ z ∉ T, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ Disjoint V T ∧
      ∃ (k : ℕ) (F : (Fin n → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ B ↔ F y = 0))
    (hpure : ∀ z ∈ B, adim2_dimension n (adim2_germ n B z) = ((p : ℕ∞) : WithBot ℕ∞))
    (hdimT : ∀ z ∈ T, adim2_dimension n (adim2_germ n T z) < ((p : ℕ∞) : WithBot ℕ∞)) :
    IsClosedAnalytic (Fin n → ℂ) (closure B) := by
  have hTloc := anr_loc_of_isClosedAnalytic T hT
  -- away from `T` the closure is the set itself, with its own local equations
  have hout : ∀ x ∉ T, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        (∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0)) ∧
        ∀ z ∈ U, (z ∈ closure B ↔ ∀ j, f j z = 0) := by
    intro x hx
    obtain ⟨V, hV, hxV, -, k, F, hF, hVB⟩ := hB x hx
    have hBV : ∀ z ∈ V, (z ∈ B ↔ ∀ j, F z j = 0) := fun z hz ↦
      (hVB z hz).trans funext_iff
    have hFa : ∀ j, AnalyticOnNhd ℂ (fun z ↦ F z j) V := fun j z hz ↦
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k ↦ ℂ) j).analyticAt _).comp
        (hF z hz)
    refine ⟨V, hV, hxV, k, fun j z ↦ F z j, hFa, hBV, fun z hz ↦ ⟨fun hzc ↦ ?_,
      fun h ↦ subset_closure ((hBV z hz).mpr h)⟩⟩
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    have hc : ContinuousAt (fun w ↦ F w j) z := (hFa j z hz).continuousAt
    rw [mem_closure_iff_frequently] at hzc
    have hVz : ∀ᶠ w in 𝓝 z, w ∈ V := hV.mem_nhds hz
    obtain ⟨w, ⟨hwB, hwV⟩, hwj⟩ :=
      ((hzc.and_eventually hVz).and_eventually (hc.eventually_ne hj)).exists
    exact hwj ((hBV w hwV).mp hwB j)
  have hclB : closure B ⊆ B ∪ T := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inr hxT
    · obtain ⟨U, -, hxU, m, f, -, hUB, hUc⟩ := hout x hxT
      exact Or.inl ((hUB x hxU).mpr ((hUc x hxU).mp hx))
  have hBloc : ∀ y ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ), (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ B ↔ ∀ j, f j z = 0) := by
    intro y hy
    obtain ⟨U, hU, hyU, m, f, hf, hUB, -⟩ :=
      hout y (fun hyT ↦ Set.disjoint_left.mp hBT hy hyT)
    exact ⟨U, hU, hyU, m, f, hf, hUB⟩
  refine anr_isClosedAnalytic_of_local (closure B) isClosed_closure fun x hx ↦ ?_
  by_cases hxT : x ∈ T
  swap
  · obtain ⟨U, hU, hxU, m, f, hf, -, hUc⟩ := hout x hxT
    exact ⟨U, hU, hxU, m, f, hf, hUc⟩
  -- at a point of `T`: the dimensions are positive and the ambient space is not a point
  obtain ⟨y, hyB⟩ : B.Nonempty := closure_nonempty_iff.mp ⟨x, hx⟩
  have hp : p ≠ 0 := by
    rintro rfl
    have hlt := hdimT x hxT
    have : Nontrivial (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n T x)) :=
      Ideal.Quotient.nontrivial_iff.mpr (adim9b_germ_ideal_ne_top n T x hxT)
    have h0 := ringKrullDim_nonneg_of_nontrivial
      (R := AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n T x))
    have h0' : ((0 : ℕ∞) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n T x) := h0
    exact absurd hlt (not_lt.mpr h0')
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 := hpure y hyB
    have h2 : adim2_dimension 0 (adim2_germ 0 B y) ≤ ringKrullDim (AnalyticGerm 0) :=
      ringKrullDim_quotient_le _
    rw [h1, adim6_parameter_dimension 0] at h2
    have : p ≤ 0 := by exact_mod_cast h2
    omega
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  have hdimT' : ∀ y ∈ T, ∀ Q ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) T y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ (d : WithBot ℕ∞) := by
    intro y hy Q hQ
    refine anr_le_of_lt_succ _ d ((anr_minimal_le_dim _ Q hQ).trans_lt ?_)
    simpa using hdimT y hy
  have hpure' := anr_pure_of_dim B hBloc (d + 1) fun z hz ↦ by simpa using hpure z hz
  exact anr_rs_local N d T B hT.1 hTloc hdimT' hBloc hpure' hclB x hxT

end HodgeLean.Foundations.Analytic
