import HodgeLean.Foundations.Program.SchlesingerPathContinue

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_coefficient_split (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E)
    (p : ι) (s : ℂ) :
    b65p_coefficient E t A s = (s - t p)⁻¹ • A p + b65p_regularPart E t A p s := by
  unfold b65p_coefficient b65p_regularPart
  have h : ∀ q, (s - t q)⁻¹ • A q =
      (if q = p then (s - t q)⁻¹ • A q else 0) +
        (if q = p then 0 else (s - t q)⁻¹ • A q) := by
    intro q
    by_cases hq : q = p <;> simp [hq]
  rw [Finset.sum_congr rfl (fun q _ ↦ h q), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem b65p_fixed_gauge_algebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : ℂ) (hw : w ≠ 0) (a a₀ R R₀ B B₀ y h h' P₀ Λ : E →L[ℂ] E)
    (hB : B = w⁻¹ • a + R) (hB₀ : B₀ = w⁻¹ • a₀ + R₀)
    (hΛ : a₀ * P₀ = P₀ * Λ) (hP₀ : P₀ * Ring.inverse P₀ = 1)
    (hh : w • h' = Λ * h - h * Λ + w • ((Ring.inverse P₀ * R₀ * P₀) * h)) :
    w • ((B * y - y * B₀) * (P₀ * h) + y * (P₀ * h')) =
      a * (y * (P₀ * h)) - y * (P₀ * h) * Λ + w • (R * (y * (P₀ * h))) := by
  have e1 : w • ((B * y - y * B₀) * (P₀ * h) + y * (P₀ * h')) =
      (w • B) * y * (P₀ * h) - y * (w • B₀) * (P₀ * h) + y * (P₀ * (w • h')) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, sub_mul, mul_assoc]
  have hwB : w • B = a + w • R := by
    rw [hB, smul_add, smul_smul, mul_inv_cancel₀ hw, one_smul]
  have hwB₀ : w • B₀ = a₀ + w • R₀ := by
    rw [hB₀, smul_add, smul_smul, mul_inv_cancel₀ hw, one_smul]
  have hΛ' : ∀ X : E →L[ℂ] E, a₀ * (P₀ * X) = P₀ * (Λ * X) := by
    intro X; rw [← mul_assoc, hΛ, mul_assoc]
  have hP₀' : ∀ X : E →L[ℂ] E, P₀ * (Ring.inverse P₀ * X) = X := by
    intro X; rw [← mul_assoc, hP₀, one_mul]
  rw [e1, hwB, hwB₀, hh]
  simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc,
    hΛ', hP₀']
  abel

theorem b65p_fixed_conj_algebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : ℂ) (Λ a Q R K K' : E →L[ℂ] E) (hQ : IsUnit Q) (ha : a * Q = Q * Λ)
    (hK : w • K' = a * K - K * Λ + w • (R * K)) :
    w • (Ring.inverse Q * K') = Λ * (Ring.inverse Q * K) - Ring.inverse Q * K * Λ +
      w • ((Ring.inverse Q * R * Q) * (Ring.inverse Q * K)) := by
  have h1 : Ring.inverse Q * Q = 1 := Ring.inverse_mul_cancel Q hQ
  have h2 : Q * Ring.inverse Q = 1 := Ring.mul_inverse_cancel Q hQ
  have hQa : Ring.inverse Q * a = Λ * Ring.inverse Q := by
    calc Ring.inverse Q * a = Ring.inverse Q * (a * Q) * Ring.inverse Q := by
          rw [mul_assoc (Ring.inverse Q) (a * Q), mul_assoc a, h2, mul_one]
      _ = Λ * Ring.inverse Q := by rw [ha, ← mul_assoc, h1, one_mul]
  have hRQ : (Ring.inverse Q * R * Q) * (Ring.inverse Q * K) = Ring.inverse Q * (R * K) := by
    rw [mul_assoc, ← mul_assoc Q, h2, one_mul, mul_assoc]
  rw [← mul_smul_comm, hK, hRQ, mul_add, mul_sub, ← mul_assoc (Ring.inverse Q) a K, hQa,
    mul_smul_comm]
  simp only [mul_assoc]

theorem b65p_schlesinger_fixed_pole_gauge (E : Type*) [NormedAddCommGroup E]
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
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  set c := t 0 p with hc
  let r' := r / 2
  have hr' : 0 < r' := by positivity
  have hr'r : r' < r := by dsimp [r']; linarith
  have hcb : closedBall (0 : ℂ) r' ⊆ ball 0 r := closedBall_subset_ball hr'r
  have hbb : ball (0 : ℂ) r' ⊆ ball 0 r := ball_subset_ball hr'r.le
  have hAa (q : ι) : AnalyticOnNhd ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) from
      fun z hz ↦ (hA z hz q).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hv : ∀ θ ∈ ball (0 : ℂ) r, deriv (fun z ↦ t z p) θ = 0 := by
    intro θ hθ
    have he : (fun z ↦ t z p) =ᶠ[𝓝 θ] fun _ ↦ c :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hθ) hp
    rw [he.deriv_eq, deriv_const]
  let K : Set ℂ := ⋃ q : {q // q ≠ p}, (fun z ↦ t z q) '' closedBall 0 r'
  have hK : IsCompact K := isCompact_iUnion (fun q ↦
    (isCompact_closedBall (0 : ℂ) r').image_of_continuousOn
      ((ht q.1).continuousOn.mono hcb))
  let V : Set ℂ := Kᶜ
  have hVo : IsOpen V := hK.isClosed.isOpen_compl
  have hV : ∀ s ∈ V, ∀ z ∈ closedBall (0 : ℂ) r', ∀ q, q ≠ p → s ≠ t z q := by
    intro s hs z hz q hq heq
    exact hs (mem_iUnion.mpr ⟨⟨q, hq⟩, z, hz, heq.symm⟩)
  have hcV : c ∈ V := by
    intro hcK
    obtain ⟨⟨q, hq⟩, z, hz, heq⟩ := mem_iUnion.mp hcK
    exact hq (hinj z (hcb hz) (heq.trans (hp z (hcb hz)).symm))
  let S' : ℂ × ℂ → E →L[ℂ] E := fun w ↦ -∑ q, if q = p then 0 else
    (deriv (fun z ↦ t z q) w.2 / (w.1 - t w.2 q)) • A w.2 q
  have hS'a : AnalyticOnNhd ℂ S' (V ×ˢ ball 0 r') := by
    intro w hw
    apply AnalyticAt.neg
    apply Finset.analyticAt_fun_sum
    intro q _
    have hz := hbb hw.2
    by_cases hq : q = p
    · simp only [hq, ite_true]
      exact analyticAt_const
    · simp only [if_neg hq]
      exact (((ht q w.2 hz).deriv.comp (x := w) (f := Prod.snd) analyticAt_snd).div
        (analyticAt_fst.sub ((ht q w.2 hz).comp (x := w) (f := Prod.snd) analyticAt_snd))
        (sub_ne_zero.mpr (hV w.1 hw.1 w.2 (ball_subset_closedBall hw.2) q hq))).smul
        ((hAa q w.2 hz).comp (x := w) (f := Prod.snd) analyticAt_snd)
  have hS'eq : ∀ s z, z ∈ ball (0 : ℂ) r → S' (s, z) =
      b65p_verticalCoefficient E (t z) (fun q ↦ deriv (fun w ↦ t w q) z) (A z) s := by
    intro s z hz
    unfold b65p_verticalCoefficient
    dsimp only [S']
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q = p
    · subst hq
      simp [hv z hz]
    · simp [hq]
  obtain ⟨Y, hYa, hY0, hYd, hYu⟩ := b65p_parameter_linear_system E S' V hVo r' hr' hS'a
  let U : Set ℂ := V ∩ {s | s ≠ c}
  have hUo : IsOpen U := hVo.inter isOpen_ne
  have hU : ∀ s ∈ U, ∀ z ∈ ball (0 : ℂ) r', ∀ q, s ≠ t z q := by
    intro s hs z hz q
    by_cases hq : q = p
    · subst hq
      rw [hp z (hbb hz)]
      exact hs.2
    · exact hV s hs.1 z (ball_subset_closedBall hz) q hq
  have hsp := b65p_schlesinger_spatial_gauge E r' hr' t A U hUo
    (fun q ↦ (ht q).mono hbb) (fun z hz ↦ hinj z (hbb hz)) (fun z hz ↦ hA z (hbb hz)) hU Y
    (hYa.mono (prod_mono inter_subset_left subset_rfl)) (fun s hs ↦ hY0 s hs.1)
    (fun s hs z hz ↦ (hYd s hs.1 z hz).congr_deriv (by rw [hS'eq s z (hbb hz)]))
  let L : ℂ → E →L[ℂ] E := fun z ↦ S' (c, z)
  have hLa : AnalyticOnNhd ℂ L (ball 0 r') := fun z hz ↦
    (hS'a (c, z) ⟨hcV, hz⟩).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hlax : ∀ z ∈ ball (0 : ℂ) r', b65p_laxGenerator E
      (fun q ↦ deriv (fun θ ↦ t θ q) z) (t z) (A z) p = L z := by
    intro z hz
    unfold b65p_laxGenerator
    dsimp only [L, S']
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q = p
    · simp [hq]
    · simp only [if_neg hq, hv z (hbb hz), hp z (hbb hz), zero_sub, neg_div, neg_smul]
  have hAL : ∀ z ∈ ball (0 : ℂ) r', HasDerivAt (fun z ↦ A z p)
      (L z * A z p - A z p * L z) z := by
    intro z hz
    apply (hA z (hbb hz) p).congr_deriv
    rw [b65p_schlesingerField_lax, hlax z hz]
  have hYc : ∀ z ∈ ball (0 : ℂ) r', HasDerivAt (fun w ↦ Y (c, w)) (L z * Y (c, z)) z :=
    fun z hz ↦ hYd c hcV z hz
  have hconj : ∀ z ∈ ball (0 : ℂ) r', A z p * Y (c, z) = Y (c, z) * A 0 p := by
    intro z hz
    refine b65p_linear_unique_center E L 0 r' hr' hLa (fun z ↦ A z p * Y (c, z))
      (fun z ↦ Y (c, z) * A 0 p) (by simp [hY0 c hcV]) (fun z hz ↦ ?_) (fun z hz ↦ ?_) hz
    · convert (hAL z hz).mul (hYc z hz) using 1
      noncomm_ring
    · convert (hYc z hz).mul_const (A 0 p) using 1
      rw [mul_assoc]
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVo c hcV
  let ε := min r' (min d δ)
  have hε : 0 < ε := lt_min hr' (lt_min hd hδ)
  have hεr' : ε ≤ r' := min_le_left _ _
  have hεd : ε ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ε ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hθε : ∀ θ ∈ ball (0 : ℂ) ε, θ ∈ ball (0 : ℂ) r' := fun θ hθ ↦ ball_subset_ball hεr' hθ
  have hsV : ∀ s ∈ ball c ε, s ∈ V := fun s hs ↦ hδV (ball_subset_ball hεδ hs)
  have hsd : ∀ s ∈ ball c ε, s ∈ ball c d := fun s hs ↦ ball_subset_ball hεd hs
  let P : ℂ → E →L[ℂ] E := fun θ ↦ Y (c, θ) * P₀
  let H : ℂ → ℂ → E →L[ℂ] E := fun s θ ↦ Ring.inverse (P θ) * (Y (s, θ) * (P₀ * H₀ s))
  have hPu : ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (P θ) :=
    fun θ hθ ↦ (hYu c hcV θ (hθε θ hθ)).mul hP₀
  have hPa : AnalyticOnNhd ℂ P (ball 0 ε) := fun θ hθ ↦
    ((hYa (c, θ) ⟨hcV, hθε θ hθ⟩).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl).mul analyticAt_const
  have hHc : ∀ θ ∈ ball (0 : ℂ) ε, H c θ = 1 := by
    intro θ hθ
    simp only [H, P, hH₀p, mul_one]
    exact Ring.inverse_mul_cancel _ (hPu θ hθ)
  refine ⟨ε, hε, hεr'.trans hr'r.le, hεd, P, H, hPa, ?_, ?_, ?_, ?_, hHc, ?_⟩
  · simp [P, hY0 c hcV]
  · intro θ hθ
    refine ⟨hPu θ hθ, ?_⟩
    simp only [P]
    rw [← mul_assoc, hconj θ (hθε θ hθ), mul_assoc, hΛ, mul_assoc]
  · intro w hw
    obtain ⟨u, hu⟩ := hPu w.2 hw.2
    have hinv : AnalyticAt ℂ (fun w : ℂ × ℂ ↦ Ring.inverse (P w.2)) w :=
      (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq
        ((hPa w.2 hw.2).comp (x := w) (f := Prod.snd) analyticAt_snd) hu.symm
    exact hinv.mul ((hYa w ⟨hsV w.1 hw.1, hθε w.2 hw.2⟩).mul
      (analyticAt_const.mul ((hH₀ w.1 (hsd w.1 hw.1)).comp (x := w) (f := Prod.fst)
        analyticAt_fst)))
  · intro s hs
    simp only [H, P, hY0 s (hsV s hs), hY0 c hcV, one_mul]
    exact Ring.inverse_mul_cancel_left _ _ hP₀
  · intro θ hθ s hs
    by_cases hsc : s = c
    · subst hsc
      rw [hHc θ hθ]
      simp
    have hsU : s ∈ U := ⟨hsV s hs, hsc⟩
    have hw : s - c ≠ 0 := sub_ne_zero.mpr hsc
    have hYs := hsp s hsU θ (hθε θ hθ)
    have hH₀d : HasDerivAt H₀ (deriv H₀ s) s :=
      (hH₀ s (hsd s hs)).differentiableAt.hasDerivAt
    have hHd : HasDerivAt (fun s ↦ H s θ) (Ring.inverse (P θ) *
        ((b65p_coefficient E (t θ) (A θ) s * Y (s, θ) -
          Y (s, θ) * b65p_coefficient E (t 0) (A 0) s) * (P₀ * H₀ s) +
          Y (s, θ) * (P₀ * deriv H₀ s))) s :=
      (hYs.fun_mul (hH₀d.const_mul P₀)).const_mul (Ring.inverse (P θ))
    rw [hHd.deriv]
    have hθr : θ ∈ ball (0 : ℂ) r := hbb (hθε θ hθ)
    apply b65p_fixed_conj_algebra E (s - c) Λ (A θ p) (P θ) _ _ _ (hPu θ hθ)
    · simp only [P]
      rw [← mul_assoc, hconj θ (hθε θ hθ), mul_assoc, hΛ, mul_assoc]
    · apply b65p_fixed_gauge_algebra E (s - c) hw (A θ p) (A 0 p)
        (b65p_regularPart E (t θ) (A θ) p s) (b65p_regularPart E (t 0) (A 0) p s)
      · rw [b65p_coefficient_split E (t θ) (A θ) p s, hp θ hθr]
      · rw [b65p_coefficient_split E (t 0) (A 0) p s]
      · exact hΛ
      · exact Ring.mul_inverse_cancel _ hP₀
      · exact hH₀eq s (hsd s hs)

end HodgeLean.Foundations.Program
