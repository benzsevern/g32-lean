import HodgeLean.Foundations.Program.SchlesingerPathDefs
import HodgeLean.Foundations.Program.SchlesingerPathODE
import HodgeLean.Foundations.Program.SchlesingerPathBase
import HodgeLean.Foundations.Program.SchlesingerPathCurve
import HodgeLean.Foundations.Program.SchlesingerPathMobius
import HodgeLean.Foundations.Program.SchlesingerPathLax
import HodgeLean.Foundations.Program.SchlesingerPathMixed
import HodgeLean.Foundations.Program.SchlesingerPathGauge
import HodgeLean.Foundations.Program.SchlesingerPathNormal
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsTransport

/-! # B6-5 stage 5c: statement bodies reserved for the proving stage. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_schlesingerField_sum (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v t : ι → ℂ) (A : ι → E →L[ℂ] E) :
    ∑ p, b65p_schlesingerField E v t A p = 0 := by
  classical
  unfold b65p_schlesingerField
  rw [← Fintype.sum_prod_type (fun a : ι × ι ↦
    if a.2 = a.1 then 0 else ((v a.1 - v a.2) / (t a.1 - t a.2)) •
      (A a.2 * A a.1 - A a.1 * A a.2))]
  apply Finset.sum_ninvolution Prod.swap
  · intro a
    rcases a with ⟨p, q⟩
    by_cases h : q = p
    · subst q; simp
    · have hratio : (v q - v p) / (t q - t p) = (v p - v q) / (t p - t q) := by
        rw [← neg_sub (v p) (v q), ← neg_sub (t p) (t q), neg_div_neg_eq]
      simp only [Prod.swap, if_neg h, if_neg (Ne.symm h), hratio]
      rw [← smul_add, sub_add_sub_cancel, sub_self, smul_zero]
  · rintro ⟨p, q⟩ h heq
    have hpq : q = p := congrArg Prod.fst heq
    subst q
    simp at h
  · intro a; exact Finset.mem_univ _
  · intro a; exact Prod.swap_swap a

theorem b65p_residue_sum_constant (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t v : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (v θ) (t θ) (A θ) p) θ) :
    ∀ θ ∈ ball (0 : ℂ) r, ∑ q, A θ q = ∑ q, A 0 q := by
  have hd : ∀ θ ∈ ball (0 : ℂ) r, HasDerivAt (fun θ ↦ ∑ q, A θ q) 0 θ := by
    intro θ hθ
    simpa only [b65p_schlesingerField_sum] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun q _ ↦ hA θ hθ q))
  intro θ hθ
  exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hd z hz).deriv) hθ (mem_ball_self (lt_of_le_of_lt dist_nonneg hθ))

theorem b65p_schlesinger_isomonodromic_aux (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) :
    (∀ θ ∈ ball (0 : ℂ) r, ∑ q, A θ q = ∑ q, A 0 q) ∧
    (∀ θ ∈ ball (0 : ℂ) r, ∀ q, ∃ G : (E →L[ℂ] E)ˣ, A θ q = G.val * A 0 q * (G⁻¹).val) ∧
    ∀ x : ℂ, ∀ θ ∈ ball (0 : ℂ) r, ∃ G : (E →L[ℂ] E)ˣ, ∀ γ : Path x x,
      (∀ θ' ∈ ball (0 : ℂ) r, ∀ s q, γ s ≠ t θ' q) →
      b65f_transport E (b65p_coefficient E (t θ) (A θ)) (fun u ↦ γ.extend u) =
        G.val * b65f_transport E (b65p_coefficient E (t 0) (A 0)) (fun u ↦ γ.extend u) *
          (G⁻¹).val := by
  refine ⟨b65p_residue_sum_constant E r t (fun θ q ↦ deriv (fun θ ↦ t θ q) θ) A hA,
    b65p_schlesinger_residue_conjugacy E r t A ht hinj hA,
    b65p_schlesinger_common_conjugator E r t A ht hinj hA⟩

theorem b65p_schlesinger_solution_aux (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : Function.Injective (t 0)) (A₀ : ι → E →L[ℂ] E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ A : ℂ → ι → E →L[ℂ] E,
      A 0 = A₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, Function.Injective (t θ)) ∧
      (∀ q, AnalyticOnNhd ℂ (fun θ ↦ A θ q) (ball 0 ρ)) ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, ∀ p, HasDerivAt (fun θ ↦ A θ p)
        (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) ∧
      ∀ ρ' : ℝ, ρ' ≤ ρ → ∀ B : ℂ → ι → E →L[ℂ] E, B 0 = A₀ →
        (∀ θ ∈ ball (0 : ℂ) ρ', ∀ p, HasDerivAt (fun θ ↦ B θ p)
          (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (B θ) p) θ) →
        ∀ θ ∈ ball (0 : ℂ) ρ', B θ = A θ := by
  classical
  let F : ℂ × (ι → E →L[ℂ] E) → (ι → E →L[ℂ] E) := fun w ↦
    b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) w.1) (t w.1) w.2
  have hF : AnalyticAt ℂ F (0, A₀) :=
    b65p_field_analytic E t r ht 0 (mem_ball_self hr) hinj A₀
  obtain ⟨ρ₀, hρ₀, A, hAa, hA0, hAd⟩ := b65p_local_ode (ι → E →L[ℂ] E) F A₀ hF
  have hei : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ p q : ι, p ≠ q → t θ p ≠ t θ q := by
    simp only [Filter.eventually_all]
    intro p q hpq
    have h := (((ht p 0 (mem_ball_self hr)).continuousAt).sub
      ((ht q 0 (mem_ball_self hr)).continuousAt)).eventually_ne
        (sub_ne_zero.mpr (fun heq ↦ hpq (hinj heq)))
    exact h.mono (fun θ hθ ↦ sub_ne_zero.mp hθ)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hei
  let ρ := min ρ₀ (min r δ)
  have hρ : 0 < ρ := lt_min hρ₀ (lt_min hr hδ)
  have hρ₀le : ρ ≤ ρ₀ := min_le_left _ _
  have hρr : ρ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, hρr, A, hA0, ?_, ?_, ?_, ?_⟩
  · intro θ hθ p q heq
    by_contra hpq
    exact hd (ball_subset_ball hρδ hθ) p q hpq heq
  · intro q
    exact (analyticOnNhd_pi_iff.mp hAa q).mono (ball_subset_ball hρ₀le)
  · intro θ hθ p
    exact hasDerivAt_pi.mp (hAd θ (ball_subset_ball hρ₀le hθ)) p
  · intro ρ' hρ' B hB0 hB θ hθ
    have hρ'pos : 0 < ρ' := lt_of_le_of_lt dist_nonneg (mem_ball.mp hθ)
    have hB' : ∀ z ∈ ball (0 : ℂ) ρ', HasDerivAt B (F (z, B z)) z := by
      intro z hz
      exact hasDerivAt_pi.mpr (hB z hz)
    exact b65p_ode_unique (ι → E →L[ℂ] E) F A₀ hF ρ' hρ'pos B A hB0 hA0 hB'
      (fun z hz ↦ hAd z (ball_subset_ball (hρ'.trans hρ₀le) hz)) hθ

theorem b65p_schlesinger_fixed_pole_aux (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ)
    (p : ι) (hp : ∀ θ ∈ ball (0 : ℂ) r, t θ p = t 0 p)
    (Λ P₀ : E →L[ℂ] E) (hP₀ : IsUnit P₀) (hΛ : A 0 p * P₀ = P₀ * Λ)
    (d : ℝ) (hd : 0 < d) (H₀ : ℂ → E →L[ℂ] E)
    (hH₀ : AnalyticOnNhd ℂ H₀ (ball (t 0 p) d)) (hH₀p : H₀ (t 0 p) = 1)
    (hH₀eq : ∀ s ∈ ball (t 0 p) d,
      (s - t 0 p) • deriv H₀ s = Λ * H₀ s - H₀ s * Λ +
        (s - t 0 p) • ((Ring.inverse P₀ * b65p_regularPart E (t 0) (A 0) p s * P₀) * H₀ s)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ε ≤ d ∧
    ∃ P : ℂ → E →L[ℂ] E, ∃ H : ℂ → ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ P (ball 0 ε) ∧ P 0 = P₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ε, IsUnit (P θ) ∧ A θ p * P θ = P θ * Λ) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ ↦ H w.1 w.2) (ball (t 0 p) ε ×ˢ ball 0 ε) ∧
      (∀ s ∈ ball (t 0 p) ε, H s 0 = H₀ s) ∧
      (∀ θ ∈ ball (0 : ℂ) ε, H (t 0 p) θ = 1) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, ∀ s ∈ ball (t 0 p) ε,
        (s - t 0 p) • deriv (fun s ↦ H s θ) s = Λ * H s θ - H s θ * Λ +
          (s - t 0 p) • ((Ring.inverse (P θ) * b65p_regularPart E (t θ) (A θ) p s * P θ) *
            H s θ) := by
  exact b65p_schlesinger_fixed_pole_gauge E r hr t A ht hinj hA p hp Λ P₀ hP₀ hΛ d hd H₀
    hH₀ hH₀p hH₀eq

theorem b65p_base_system_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Function.Injective (b65p_poles p 0) ∧
    (∀ s : ℂ, s ∈ b65s_regular ↔ ∀ q, s ≠ b65p_poles p 0 q) ∧
    ∀ s ∈ b65s_regular,
      b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue s = b65r_pullback s := by
  classical
  have hpinj := b65p_boxes_injective p (fun k ↦ ⟨(hp k).1, (hp k).2.1⟩)
  have hidx : Function.Surjective b65b_boxIndex := by decide
  have hroot : ∀ j, b65r_P (b65p_fibre j) (p j) = 0 := by
    intro j
    obtain ⟨k, rfl⟩ := hidx j
    rw [b65p_label_fibre]
    exact (hp k).2.2
  have hfibre : ∀ j, b65p_fibre j = 5 ∨ b65p_fibre j = -7 := by decide
  have hfixed : Function.Injective b65p_fixedPole := by
    intro k l h
    fin_cases k <;> fin_cases l <;> first | rfl | (exfalso; norm_num [b65p_fixedPole] at h)
  have hne : ∀ j k, p j ≠ b65p_fixedPole k := by
    intro j k h
    have hz := hroot j
    rw [h] at hz
    rcases hfibre j with he | he <;> rw [he] at hz <;>
      fin_cases k <;> norm_num [b65p_fixedPole, b65r_P] at hz
  have hzero : ∀ (e : ℤ), e = 5 ∨ e = -7 → ∀ s,
      b65r_P e s = 0 ↔ ∃ j ∈ b65p_fibreLabels e, p j = s := by
    intro e he s
    have he1 : (e : ℂ) ≠ 1 := by rcases he with rfl | rfl <;> norm_num
    rw [← b65s_poly_eval]
    change (b65s_poly e).IsRoot s ↔ _
    rw [← Polynomial.mem_roots (b65s_poly_ne_zero _ he1),
      b65p_fibre_roots p hpinj hroot e he, Finset.mem_val, Finset.mem_image]
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    simp only [b65p_poles, zero_mul, add_zero] at h
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (hfixed h)
    · exact (hne b a h.symm).elim
    · exact (hne a b h).elim
    · exact congrArg Sum.inr (hpinj h)
  · intro s
    constructor
    · intro hs q
      rcases q with k | j
      · fin_cases k
        · exact hs.1
        · exact hs.2.1
        · exact hs.2.2.1
        · exact hs.2.2.2.1
      · intro heq
        have hz := hroot j
        have heq' : s = p j := by simpa [b65p_poles] using heq
        rw [← heq'] at hz
        rcases hfibre j with hf | hf
        · rw [hf] at hz; exact hs.2.2.2.2.1 hz
        · rw [hf] at hz; exact hs.2.2.2.2.2 (by simpa only [Int.cast_neg, Int.cast_ofNat] using hz)
    · intro hs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [b65p_poles, b65p_fixedPole] using hs (Sum.inl 0)
      · simpa [b65p_poles, b65p_fixedPole] using hs (Sum.inl 1)
      · simpa [b65p_poles, b65p_fixedPole] using hs (Sum.inl 2)
      · simpa [b65p_poles, b65p_fixedPole] using hs (Sum.inl 3)
      · intro hz
        obtain ⟨j, _, hj⟩ := (hzero 5 (Or.inl rfl) s).mp hz
        exact hs (Sum.inr j) (by simpa [b65p_poles] using hj.symm)
      · intro hz
        obtain ⟨j, _, hj⟩ := (hzero (-7) (Or.inr rfl) s).mp (by simpa only [Int.cast_neg, Int.cast_ofNat] using hz)
        exact hs (Sum.inr j) (by simpa [b65p_poles] using hj.symm)
  · intro s hs
    have h5 := b65p_fibre_logDeriv p hpinj hroot 5 (Or.inl rfl) s hs.2.2.2.2.1
    have h7 := b65p_fibre_logDeriv p hpinj hroot (-7) (Or.inr rfl) s (by simpa only [Int.cast_neg, Int.cast_ofNat] using hs.2.2.2.2.2)
    norm_num only [Int.cast_neg, Int.cast_ofNat] at h5 h7
    have hS5 : b65p_fibreLabels 5 = {1, 3, 5, 6, 9, 10} := by decide
    have hS7 : b65p_fibreLabels (-7) = {0, 2, 4, 7, 8, 11} := by decide
    simp only [hS5, hS7] at h5 h7
    norm_num at h5 h7
    unfold b65r_pullback
    rw [h5, h7]
    simp only [b65p_coefficient, Fintype.sum_sum_type, b65p_poles, b65p_initialResidue,
      Sum.elim_inl, Sum.elim_inr, zero_mul, add_zero]
    simp only [b65p_movingResidue, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Finset.sum_filter, b65p_fibre, b65p_fixedResidue,
      b65p_fixedPole, Matrix.cons_val_zero, Matrix.cons_val_succ]
    have hop : ∀ (c : ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ),
        b65r_operator (c • B) = c • b65r_operator B := by
      intro c B; ext v i; simp [b65r_operator]
    simp only [hop, smul_smul, add_smul, div_eq_mul_inv, smul_add]
    norm_num
    module

theorem b65p_base_normal_form_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (k : Fin 4) (P₀ : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (hP₀ : IsUnit P₀)
    (hΛ : b65p_initialResidue (Sum.inl k) * P₀ = P₀ * b65p_exponent k) :
    ∃ d : ℝ, 0 < d ∧ ∃ H₀ : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      AnalyticOnNhd ℂ H₀ (ball (b65p_fixedPole k) d) ∧ H₀ (b65p_fixedPole k) = 1 ∧
      ∀ s ∈ ball (b65p_fixedPole k) d,
        (s - b65p_fixedPole k) • deriv H₀ s =
          b65p_exponent k * H₀ s - H₀ s * b65p_exponent k +
            (s - b65p_fixedPole k) • ((Ring.inverse P₀ *
              b65p_regularPart (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue (Sum.inl k) s *
                P₀) * H₀ s) := by
  obtain ⟨hinj, hreg, hcoeff⟩ := b65p_base_system_aux p hp
  exact b65p_base_normal_form_of p hinj hreg hcoeff k P₀ hP₀ hΛ

theorem b65p_marked_monodromy_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (r : ℝ) (hr : 0 < r) (A : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (hA0 : A 0 = b65p_initialResidue)
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ q, HasDerivAt (fun θ ↦ A θ q)
      (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (A θ) q) θ)
    (x : b65s_regular) (γ : Fin 13 → Path x x) (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ i, b65p_certifiedTransport x γ i =
      C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∀ θ ∈ ball (0 : ℂ) r',
      (∀ i s q, ((γ i s : b65s_regular) : ℂ) ≠ b65p_poles p θ q) ∧
      ∃ Cθ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ i,
        b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (A θ))
            (fun u ↦ ((γ i.rev).extend u).val) =
          Cθ.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (Cθ⁻¹).val := by
  have htder : ∀ q θ, HasDerivAt (fun θ ↦ b65p_poles p θ q) (b65p_velocity p q) θ := by
    intro q θ
    rcases q with k | j
    · simpa [b65p_poles, b65p_velocity] using hasDerivAt_const θ (b65p_fixedPole k)
    · simpa [b65p_poles, b65p_velocity] using
        ((hasDerivAt_id θ).mul_const (b65p_V (b65p_fibre j) (p j))).const_add (p j)
  have ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) Set.univ := by
    intro q θ _
    rcases q with k | j
    · exact analyticAt_const
    · exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  obtain ⟨hinj, hreg, hcoeff⟩ := b65p_base_system_aux p hp
  have hei : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ i : Fin 13, ∀ q : Fin 4 ⊕ Fin 12,
      b65p_poles p θ q ∉ Set.range (fun s ↦ ((γ i s : b65s_regular) : ℂ)) := by
    simp only [Filter.eventually_all]
    intro i q
    have hcompact := isCompact_range (continuous_subtype_val.comp (γ i).continuous)
    have hnot : b65p_poles p 0 q ∉ Set.range (fun s ↦ ((γ i s : b65s_regular) : ℂ)) := by
      rintro ⟨s, hs⟩
      exact (hreg _).mp (γ i s).property q hs
    exact (htder q 0).continuousAt.eventually (hcompact.isClosed.isOpen_compl.mem_nhds hnot)
  have hinje : ∀ᶠ θ in 𝓝 (0 : ℂ), Function.Injective (b65p_poles p θ) := by
    have he : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ q j : Fin 4 ⊕ Fin 12,
        q ≠ j → b65p_poles p θ q ≠ b65p_poles p θ j := by
      simp only [Filter.eventually_all]
      intro q j hqj
      have h := ((htder q 0).continuousAt.sub (htder j 0).continuousAt).eventually_ne
        (sub_ne_zero.mpr (fun heq ↦ hqj (hinj heq)))
      exact h.mono (fun θ hθ ↦ sub_ne_zero.mp hθ)
    exact he.mono (fun θ h q j heq ↦ by by_contra hne; exact h q j hne heq)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (hei.and hinje)
  let r' := min r δ
  have hr' : 0 < r' := lt_min hr hδ
  have hrr : r' ≤ r := min_le_left _ _
  have hrd : r' ≤ δ := min_le_right _ _
  have havoid : ∀ θ ∈ ball (0 : ℂ) r', ∀ i s q,
      ((γ i s : b65s_regular) : ℂ) ≠ b65p_poles p θ q := by
    intro θ hθ i s q heq
    exact (hd (ball_subset_ball hrd hθ)).1 i q ⟨s, heq⟩
  have hregopen : IsOpen b65s_regular := by
    have heq : b65s_regular = ⋂ q, {s : ℂ | s ≠ b65p_poles p 0 q} := by
      ext s
      simpa only [mem_iInter, mem_setOf_eq] using hreg s
    rw [heq]
    exact isOpen_iInter_of_finite (fun _ ↦ isOpen_ne)
  refine ⟨r', hr', hrr, fun θ hθ ↦ ⟨havoid θ hθ, ?_⟩⟩
  obtain ⟨G, hG⟩ := (b65p_schlesinger_isomonodromic_aux (Fin 4 → ℂ) r' (b65p_poles p) A
    (fun q ↦ (ht q).mono (Set.subset_univ _))
    (fun z hz ↦ (hd (ball_subset_ball hrd hz)).2)
    (by simpa only [(htder _ _).deriv] using
      (fun z hz ↦ hA z (ball_subset_ball hrr hz)))).2.2 x θ hθ
  refine ⟨G * C, fun i ↦ ?_⟩
  have hGi := hG ((γ i.rev).map continuous_subtype_val)
    (fun z hz s q ↦ havoid z hz i.rev s q)
  have hbase : b65f_transport (Fin 4 → ℂ)
      (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) (A 0))
      (fun u ↦ ((γ i.rev).extend u).val) = b65p_certifiedTransport x γ i := by
    apply b65t_transport_congr hregopen
      (by intro s hs; simpa only [hA0] using hcoeff s hs)
      (fun u ↦ ((γ i.rev).extend u).val)
      (continuous_subtype_val.comp (γ i.rev).continuous_extend).continuousOn
    intro u _
    exact ((γ i.rev).extend u).property
  have hext : (fun u ↦ (((γ i.rev).map continuous_subtype_val).extend u)) =
      (fun u ↦ ((γ i.rev).extend u).val) := by
    funext u
    rfl
  rw [hext, hbase, hT i] at hGi
  simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using hGi

theorem b65p_normalized_path_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    (∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6_chart ∧
      ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
        ⇑M = b65p_mobius (b65p_moving p θ 10) (b65p_moving p θ 11) ∧
          ∀ k, M (b65p_source p θ k) = b6_branch (b65p_curve p θ) k) ∧
    AnalyticAt ℂ (b65p_curve p) 0 ∧ deriv (b65p_curve p) 0 ≠ 0 ∧
    ContinuousAt (b65p_curve p) 0 ∧
    b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6t_polydisc (b65p_curve p 0) := by
  have hpinj := b65p_boxes_injective p (fun k ↦ ⟨(hp k).1, (hp k).2.1⟩)
  have hi := (b65p_base_system_aux p hp).1
  have hne (j : Fin 12) : p j ≠ 0 := by
    intro hj
    have he : b65p_poles p 0 (Sum.inr j) = b65p_poles p 0 (Sum.inl 0) := by
      simpa [b65p_poles, b65p_fixedPole] using hj
    have := hi he
    cases this
  obtain ⟨ha, hc, hp0, hlocal⟩ := b65p_curve_local p hpinj hne
  refine ⟨?_, ha, b65p_curve_deriv_ne_zero p hpinj hne, hc, hp0,
    hlocal.mono (fun _ h ↦ h.1)⟩
  filter_upwards [b65p_moving_eventually_separated p hpinj hne] with θ hθ
  have hab : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 :=
    sub_ne_zero.mpr (fun he ↦ by have := hθ.1 he; norm_num at this)
  refine ⟨b65p_chartPoint_mem _ hθ.1 hθ.2,
    b65p_mobiusHomeomorph _ _ (hθ.2 10) (hθ.2 11) hab,
    b65p_mobiusHomeomorph_apply _ _ (hθ.2 10) (hθ.2 11) hab, ?_⟩
  intro k
  rw [b65p_mobiusHomeomorph_apply]
  exact b65p_mobius_labels _ hθ.2 hab k

theorem b65p_outputs_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Nonempty (b65p_Outputs p) := by
  have htder : ∀ q θ, HasDerivAt (fun θ ↦ b65p_poles p θ q) (b65p_velocity p q) θ := by
    intro q θ
    rcases q with k | j
    · simpa [b65p_poles, b65p_velocity] using hasDerivAt_const θ (b65p_fixedPole k)
    · simpa [b65p_poles, b65p_velocity] using
        ((hasDerivAt_id θ).mul_const (b65p_V (b65p_fibre j) (p j))).const_add (p j)
  have ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) (Set.univ) := by
    intro q θ _
    rcases q with k | j
    · exact analyticAt_const
    · exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  obtain ⟨hinj, hreg, hcoeff⟩ := b65p_base_system_aux p hp
  obtain ⟨ρ, hρ, _, A, hA0, hAi, hAa, hAd, _⟩ :=
    b65p_schlesinger_solution_aux (Fin 4 → ℂ) 1 (by norm_num)
      (b65p_poles p) (fun q ↦ (ht q).mono (Set.subset_univ _)) hinj b65p_initialResidue
  have hAd' : ∀ θ ∈ ball (0 : ℂ) ρ, ∀ q, HasDerivAt (fun θ ↦ A θ q)
      (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (A θ) q) θ := by
    simpa only [(htder _ _).deriv] using hAd
  obtain ⟨hnorm, _, _, hcont, hzero, hpoly⟩ := b65p_normalized_path_aux p hp
  obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhds_iff.mp (hnorm.and hpoly)
  let r := min ρ δ
  have hr : 0 < r := lt_min hρ hδ
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrδ : r ≤ δ := min_le_right _ _
  have hsum0 : ∑ q, b65p_initialResidue q = 0 := by
    have key : ∑ k, b65p_fixedResidue k + ∑ j, b65p_movingResidue j = 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedResidue, b65p_movingResidue,
        b65p_fibre]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num [b65r_Binf]
      module
    have hsum : ∀ {n : Type} [Fintype n] (f : n → Matrix (Fin 4) (Fin 4) ℂ),
        b65r_operator (∑ j, f j) = ∑ j, b65r_operator (f j) := by
      intro n _ f; ext v i; simp [b65r_operator]
    have h := congrArg b65r_operator key
    rw [show b65r_operator (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 by
      ext v i; simp [b65r_operator]] at h
    rw [← h, Fintype.sum_sum_type]
    simp only [b65p_initialResidue, Sum.elim_inl, Sum.elim_inr]
    rw [← hsum, ← hsum]
    ext v i; simp [b65r_operator]
  refine ⟨{
    radius := r, radius_pos := hr, residue := A, residue_zero := hA0,
    residue_analytic := fun q ↦ (hAa q).mono (ball_subset_ball hrρ),
    schlesinger := fun θ hθ ↦ hAd' θ (ball_subset_ball hrρ hθ),
    poles_injective := fun θ hθ ↦ hAi θ (ball_subset_ball hrρ hθ),
    residue_sum := ?_, base_coefficient := ?_, curve_cont := hcont, curve_zero := hzero,
    curve_mem := ?_, normalization := ?_, normal_form := ?_, marking := ?_ }⟩
  · intro θ hθ
    rw [b65p_residue_sum_constant (Fin 4 → ℂ) ρ (b65p_poles p)
      (fun _ ↦ b65p_velocity p) A hAd' θ (ball_subset_ball hrρ hθ), hA0, hsum0]
  · simpa only [hA0] using hcoeff
  · intro θ hθ
    have h := hδmem (ball_subset_ball hrδ hθ)
    exact ⟨h.2, h.1.1⟩
  · intro θ hθ
    exact (hδmem (ball_subset_ball hrδ hθ)).1.2
  · intro k P₀ hP₀ hΛ
    rw [hA0] at hΛ
    obtain ⟨d, hd, H₀, hH₀, hH₀p, hH₀eq⟩ := b65p_base_normal_form_aux p hp k P₀ hP₀ hΛ
    obtain ⟨ε, hε, hεr, _, P, H, hP, hP0, hPΛ, hH, _, hHp, hHeq⟩ :=
      b65p_schlesinger_fixed_pole_aux (Fin 4 → ℂ) r hr (b65p_poles p) A
        (fun q ↦ (ht q).mono (Set.subset_univ _))
        (fun θ hθ ↦ hAi θ (ball_subset_ball hrρ hθ))
        (fun θ hθ ↦ hAd θ (ball_subset_ball hrρ hθ)) (Sum.inl k)
        (by intros; rfl) (b65p_exponent k) P₀ hP₀ (by simpa only [hA0] using hΛ)
        d hd H₀ hH₀ hH₀p (by simpa only [hA0, b65p_poles, Sum.elim_inl] using hH₀eq)
    exact ⟨ε, hε, hεr, P, H, hP, hP0, hPΛ, hH, hHp, hHeq⟩
  · exact b65p_marked_monodromy_aux p hp r hr A hA0
      (fun θ hθ ↦ hAd' θ (ball_subset_ball hrρ hθ))

end HodgeLean.Foundations.Program
