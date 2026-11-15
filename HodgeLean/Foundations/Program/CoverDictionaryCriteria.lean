import HodgeLean.Foundations.Program.CoverDictionaryPoles

/-! # B6-5 stage 5d, stage four: holomorphy criteria for the local forms

General statements in one complex variable. Let `s = t₀ + κᵉ` near `z₀` with `κ` a local
parameter, and `Y = M(s) · diag(κ^{mᵢ}) · K` on a punctured disc, `M` analytic and invertible at
`t₀`. Then the germs `(v ⬝ Y⁻¹ R(s)) s'` are bounded for every `v` exactly when
`ord_{t₀} (M⁻¹ R)ᵢ ≥ mᵢ / e` for every `i` (`caf_pole_rForm_iff`), and the germs
`(v ⬝ Yᵀ Q(s)) s'` are bounded for every `v` exactly when `ord_{t₀} (Mᵀ Q)ᵢ ≥ (−mᵢ) / e`
(`caf_pole_qForm_iff`). Over `s = ∞` (`1/s = κᵉ`, `Y = Φ K`, `Φ` analytic and invertible at
`z₀`) the conditions are `ord₀ R(1/w) ≥ 2`, resp. `ord₀ Q(1/w) ≥ 2` (`caf_infty_rForm_iff`,
`caf_infty_qForm_iff`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- **The derivative of `t₀ + κᵉ`** has order `e − 1`. -/
theorem caf_deriv_param (s l : ℂ → ℂ) (z₀ t₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, s z = t₀ + ((z - z₀) * l z) ^ e) :
    AnalyticAt ℂ (deriv s) z₀ ∧ meromorphicOrderAt (deriv s) z₀ = (((e : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hsa : AnalyticAt ℂ s z₀ := by
    have : AnalyticAt ℂ (fun z ↦ t₀ + κ z ^ e) z₀ := analyticAt_const.add (hκ.pow e)
    exact this.congr (hs.mono fun z hz ↦ hz.symm)
  have hd : deriv s =ᶠ[𝓝 z₀] fun z ↦ (e : ℂ) * κ z ^ (e - 1) * deriv κ z := by
    filter_upwards [hs.eventually_nhds, hκ.eventually_analyticAt] with z hz hκz
    have hz' : s =ᶠ[𝓝 z] fun x ↦ t₀ + κ x ^ e := hz
    rw [hz'.deriv_eq]
    exact ((hκz.differentiableAt.hasDerivAt.pow e).const_add t₀).deriv
  have hκ0 : κ z₀ = 0 := by simp [κ]
  have hκ' : deriv κ z₀ = l z₀ := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    exact h.deriv
  refine ⟨hsa.deriv, ?_⟩
  rw [meromorphicOrderAt_congr (nhdsWithin_le_nhds hd)]
  have h2 : AnalyticAt ℂ (deriv κ) z₀ := hκ.deriv
  have hκo := caf_order_param κ z₀ hκ hκ0 (by rw [hκ']; exact hl0)
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [show (fun z ↦ (e : ℂ) * κ z ^ (e - 1) * deriv κ z) =
      (fun _ ↦ (e : ℂ)) * (κ ^ (e - 1) * deriv κ) by funext z; simp [mul_assoc],
    meromorphicOrderAt_mul (MeromorphicAt.const _ _) ((hκ.meromorphicAt.pow _).mul
      h2.meromorphicAt), meromorphicOrderAt_mul (hκ.meromorphicAt.pow _) h2.meromorphicAt,
    meromorphicOrderAt_pow hκ.meromorphicAt, hκo, meromorphicOrderAt_const,
    h2.meromorphicOrderAt_eq, h2.analyticOrderAt_eq_zero.mpr (by rw [hκ']; exact hl0)]
  simp only [he0, ↓reduceIte, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, mul_one,
    zero_add, add_zero]
  have : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
  rw [← this]
  rfl


/-- Boundedness on a punctured neighbourhood depends only on the germ there. -/
theorem caf_bdd_congr {E : Type*} [NormedAddCommGroup E] {f g : ℂ → E} {z₀ : ℂ}
    (h : f =ᶠ[𝓝[≠] z₀] g) :
    (∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖f z‖ ≤ B) ↔ ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖g z‖ ≤ B := by
  constructor <;> rintro ⟨B, hB⟩ <;> refine ⟨B, ?_⟩ <;> filter_upwards [hB, h] with z h1 h2
  · rwa [← h2]
  · rwa [h2]

/-- The inverse of `M · diag(κ^m) · K`. -/
theorem caf_inv_local (M K : Matrix (Fin 4) (Fin 4) ℂ) (κ : ℂ) (hκ : κ ≠ 0) (m : Fin 4 → ℤ) :
    (M * diagonal (fun i ↦ κ ^ m i) * K)⁻¹ = K⁻¹ * diagonal (fun i ↦ κ ^ (-m i)) * M⁻¹ := by
  have hd : (diagonal (fun i ↦ κ ^ m i))⁻¹ = diagonal (fun i ↦ κ ^ (-m i)) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hκ, neg_add_cancel, zpow_zero]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hd, ← mul_assoc]

/-- **The holomorphy criterion for r-forms at a pole.** -/
theorem caf_pole_rForm_iff (s l : ℂ → ℂ) (z₀ t₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, s z = t₀ + ((z - z₀) * l z) ^ e)
    (M : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hM : ∀ i j, AnalyticAt ℂ (fun σ ↦ M σ i j) t₀)
    (hMd : (M t₀).det ≠ 0) (m : Fin 4 → ℤ) (Km : Matrix (Fin 4) (Fin 4) ℂ) (hK : IsUnit Km.det)
    (Ym : ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hY : ∀ᶠ z in 𝓝[≠] z₀, Ym z = M (s z) * diagonal (fun i ↦ ((z - z₀) * l z) ^ m i) * Km)
    (Rv : ℂ → Fin 4 → ℂ) (hR : ∀ j, MeromorphicAt (fun σ ↦ Rv σ j) t₀) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
        ‖(v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ i, ((m i / e : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun σ ↦ ((M σ)⁻¹ *ᵥ Rv σ) i) t₀ := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hκ0 : κ z₀ = 0 := by simp [κ]
  have hκ' : deriv κ z₀ ≠ 0 := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
  obtain ⟨hMi, hMev⟩ := caf_inv_entries_analyticAt M t₀ hM hMd
  set ρ : ℂ → Fin 4 → ℂ := fun σ ↦ (M σ)⁻¹ *ᵥ Rv σ
  have hρ : ∀ i, MeromorphicAt (fun σ ↦ ρ σ i) t₀ := fun i ↦
    caf_meromorphic_mulVec _ _ t₀ (fun i j ↦ (hMi i j).meromorphicAt) hR i
  obtain ⟨hda, hdo⟩ := caf_deriv_param s l z₀ t₀ e he hl hl0 hs
  set F : ℂ → Fin 4 → ℂ := fun z i ↦ κ z ^ (-(m i)) * (fun σ ↦ ρ σ i) (t₀ + κ z ^ e) * deriv s z
  have hF : ∀ i, MeromorphicAt (fun z ↦ F z i) z₀ := fun i ↦
    (caf_order_comp_mul (fun σ ↦ ρ σ i) t₀ z₀ κ (deriv s) hκ hκ0 hκ' e he (hρ i)
      hda.meromorphicAt (-(m i))).1
  have hKi : IsUnit (Km⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hK.ringInverse
  have heq : ∀ v : Fin 4 → ℂ, (fun z ↦ (v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z) =ᶠ[𝓝[≠] z₀]
      fun z ↦ v ⬝ᵥ (Km⁻¹ *ᵥ F z) := by
    intro v
    have hκne : ∀ᶠ z in 𝓝[≠] z₀, κ z ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hl.continuousAt.eventually_ne hl0), self_mem_nhdsWithin]
        with z hz hzz
      exact mul_ne_zero (sub_ne_zero.mpr hzz) hz
    filter_upwards [hY, nhdsWithin_le_nhds hs, hκne] with z hYz hsz hκz
    rw [hYz, caf_inv_local _ _ _ hκz, hsz]
    simp only [F, ρ, ← Matrix.mulVec_mulVec]
    rw [mul_comm, ← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul]
    congr 2
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, κ]
    ring
  rw [show (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
      ‖(v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖v ⬝ᵥ (Km⁻¹ *ᵥ F z)‖ ≤ B from
    forall_congr' fun v ↦ caf_bdd_congr (heq v), caf_bdd_vec_iff _ hKi F z₀ hF]
  refine forall_congr' fun i ↦ ?_
  refine caf_order_comp_mul_nonneg_iff (fun σ ↦ ρ σ i) t₀ z₀ κ (deriv s) hκ hκ0 hκ' e he (hρ i)
    hda.meromorphicAt ((e : ℤ) - 1) hdo (-(m i)) (m i / e) fun o ↦ ?_
  rw [caf_int_div_le_iff e he, neg_neg]

/-- **The holomorphy criterion for q-forms at a pole.** -/
theorem caf_pole_qForm_iff (s l : ℂ → ℂ) (z₀ t₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, s z = t₀ + ((z - z₀) * l z) ^ e)
    (M : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hM : ∀ i j, AnalyticAt ℂ (fun σ ↦ M σ i j) t₀)
    (m : Fin 4 → ℤ) (Km : Matrix (Fin 4) (Fin 4) ℂ) (hK : IsUnit Km.det)
    (Ym : ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hY : ∀ᶠ z in 𝓝[≠] z₀, Ym z = M (s z) * diagonal (fun i ↦ ((z - z₀) * l z) ^ m i) * Km)
    (Qv : ℂ → Fin 4 → ℂ) (hQ : ∀ j, MeromorphicAt (fun σ ↦ Qv σ j) t₀) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
        ‖(v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ i, (((-m i) / e : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun σ ↦ ((M σ)ᵀ *ᵥ Qv σ) i) t₀ := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hκ0 : κ z₀ = 0 := by simp [κ]
  have hκ' : deriv κ z₀ ≠ 0 := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
  set ρ : ℂ → Fin 4 → ℂ := fun σ ↦ (M σ)ᵀ *ᵥ Qv σ
  have hρ : ∀ i, MeromorphicAt (fun σ ↦ ρ σ i) t₀ := fun i ↦
    caf_meromorphic_mulVec _ _ t₀ (fun i j ↦ (hM j i).meromorphicAt) hQ i
  obtain ⟨hda, hdo⟩ := caf_deriv_param s l z₀ t₀ e he hl hl0 hs
  set F : ℂ → Fin 4 → ℂ := fun z i ↦ κ z ^ (m i) * (fun σ ↦ ρ σ i) (t₀ + κ z ^ e) * deriv s z
  have hF : ∀ i, MeromorphicAt (fun z ↦ F z i) z₀ := fun i ↦
    (caf_order_comp_mul (fun σ ↦ ρ σ i) t₀ z₀ κ (deriv s) hκ hκ0 hκ' e he (hρ i)
      hda.meromorphicAt (m i)).1
  have hKt : IsUnit (Kmᵀ).det := by rw [Matrix.det_transpose]; exact hK
  have heq : ∀ v : Fin 4 → ℂ, (fun z ↦ (v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z) =ᶠ[𝓝[≠] z₀]
      fun z ↦ v ⬝ᵥ (Kmᵀ *ᵥ F z) := by
    intro v
    filter_upwards [hY, nhdsWithin_le_nhds hs] with z hYz hsz
    rw [hYz, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, hsz]
    simp only [F, ρ, ← Matrix.mulVec_mulVec]
    rw [mul_comm, ← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul]
    congr 2
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, κ]
    ring
  rw [show (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
      ‖(v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖v ⬝ᵥ (Kmᵀ *ᵥ F z)‖ ≤ B from
    forall_congr' fun v ↦ caf_bdd_congr (heq v), caf_bdd_vec_iff _ hKt F z₀ hF]
  refine forall_congr' fun i ↦ ?_
  exact caf_order_comp_mul_nonneg_iff (fun σ ↦ ρ σ i) t₀ z₀ κ (deriv s) hκ hκ0 hκ' e he (hρ i)
    hda.meromorphicAt ((e : ℤ) - 1) hdo (m i) ((-m i) / e) fun o ↦ caf_int_div_le_iff e he _ o


/-- The derivative of `s` with `1/s = κᵉ` on a punctured disc: `s' = κ^{−2e} · (−(κᵉ)')`. -/
theorem caf_deriv_infty (s l : ℂ → ℂ) (z₀ : ℂ) (e : ℕ) (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, (s z)⁻¹ = ((z - z₀) * l z) ^ e) :
    ∀ᶠ z in 𝓝[≠] z₀, ((z - z₀) * l z) ≠ 0 ∧ s z = (((z - z₀) * l z) ^ e)⁻¹ ∧
      deriv s z = ((z - z₀) * l z) ^ (-(2 * e : ℤ)) *
        -deriv (fun y ↦ ((y - z₀) * l y) ^ e) z := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hκne : ∀ᶠ z in 𝓝[≠] z₀, κ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (hl.continuousAt.eventually_ne hl0), self_mem_nhdsWithin]
      with z hz hzz
    exact mul_ne_zero (sub_ne_zero.mpr hzz) hz
  have hs' : ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ y in 𝓝 z, κ y ≠ 0 ∧ s y = (κ y ^ e)⁻¹ := by
    have h1 : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → κ z ≠ 0 ∧ s z = (κ z ^ e)⁻¹ := by
      filter_upwards [hs, eventually_nhdsWithin_iff.mp hκne] with z hz hzk hzz
      refine ⟨hzk hzz, ?_⟩
      rw [← hz, inv_inv]
    filter_upwards [nhdsWithin_le_nhds h1.eventually_nhds, self_mem_nhdsWithin] with z hz hzz
    filter_upwards [hz, isOpen_compl_singleton.mem_nhds hzz] with y hy hyy
    exact hy hyy
  filter_upwards [hs', hκne, nhdsWithin_le_nhds hκ.eventually_analyticAt] with z hz hκz hκa
  refine ⟨hκz, hz.self_of_nhds.2, ?_⟩
  have hpow : HasDerivAt (fun y ↦ κ y ^ e) (deriv (fun y ↦ κ y ^ e) z) z :=
    (hκa.differentiableAt.pow e).hasDerivAt
  have hinv := hpow.inv (pow_ne_zero e hκz)
  have h2 : s =ᶠ[𝓝 z] fun y ↦ (κ y ^ e)⁻¹ := hz.mono fun y hy ↦ hy.2
  rw [(hinv.congr_of_eventuallyEq h2).deriv]
  have : κ z ^ (-(2 * e : ℤ)) = ((κ z ^ e) ^ 2)⁻¹ := by
    rw [_root_.zpow_neg, ← pow_mul, mul_comm, show ((e : ℤ) * 2) = ((e * 2 : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast]
  rw [this]
  ring

/-- **The holomorphy criterion for r-forms over `s = ∞`.** -/
theorem caf_infty_rForm_iff (s l : ℂ → ℂ) (z₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, (s z)⁻¹ = ((z - z₀) * l z) ^ e)
    (Φ : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hΦ : ∀ i j, AnalyticAt ℂ (fun z ↦ Φ z i j) z₀)
    (hΦd : (Φ z₀).det ≠ 0) (Km : Matrix (Fin 4) (Fin 4) ℂ) (hK : IsUnit Km.det)
    (Ym : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hY : ∀ᶠ z in 𝓝[≠] z₀, Ym z = Φ z * Km)
    (Rv : ℂ → Fin 4 → ℂ) (hR : ∀ j, MeromorphicAt (fun w ↦ Rv w⁻¹ j) 0) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
        ‖(v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ j, (2 : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ Rv w⁻¹ j) 0 := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hκ0 : κ z₀ = 0 := by simp [κ]
  have hκ' : deriv κ z₀ ≠ 0 := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
  obtain ⟨hua, huo⟩ := caf_deriv_param (fun z ↦ 0 + κ z ^ e) l z₀ 0 e he hl hl0
    (Eventually.of_forall fun z ↦ rfl)
  set u : ℂ → ℂ := fun z ↦ -deriv (fun y ↦ 0 + κ y ^ e) z
  have hu : AnalyticAt ℂ u z₀ := hua.neg
  have huo' : meromorphicOrderAt u z₀ = (((e : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [show u = -deriv (fun y ↦ 0 + κ y ^ e) from rfl, ← meromorphicOrderAt_neg, huo]
  obtain ⟨hΦi, -⟩ := caf_inv_entries_analyticAt Φ z₀ hΦ hΦd
  set F : ℂ → Fin 4 → ℂ := fun z j ↦ κ z ^ (-(2 * e : ℤ)) * (fun w ↦ Rv w⁻¹ j) (0 + κ z ^ e) * u z
  have hF : ∀ j, MeromorphicAt (fun z ↦ F z j) z₀ := fun j ↦
    (caf_order_comp_mul (fun w ↦ Rv w⁻¹ j) 0 z₀ κ u hκ hκ0 hκ' e he (hR j)
      hu.meromorphicAt _).1
  have hF' : ∀ i, MeromorphicAt (fun z ↦ ((Φ z)⁻¹ *ᵥ F z) i) z₀ := fun i ↦
    caf_meromorphic_mulVec _ _ z₀ (fun i j ↦ (hΦi i j).meromorphicAt) hF i
  have hKi : IsUnit (Km⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hK.ringInverse
  have heq : ∀ v : Fin 4 → ℂ, (fun z ↦ (v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z) =ᶠ[𝓝[≠] z₀]
      fun z ↦ v ⬝ᵥ (Km⁻¹ *ᵥ ((Φ z)⁻¹ *ᵥ F z)) := by
    intro v
    filter_upwards [hY, caf_deriv_infty s l z₀ e hl hl0 hs] with z hYz ⟨hκz, hsz, hdz⟩
    rw [hYz, Matrix.mul_inv_rev, hsz, hdz, ← Matrix.mulVec_mulVec]
    rw [mul_comm, ← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    congr 3
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, F, u, zero_add, κ]
    ring
  rw [show (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
      ‖(v ⬝ᵥ ((Ym z)⁻¹ *ᵥ Rv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖v ⬝ᵥ (Km⁻¹ *ᵥ ((Φ z)⁻¹ *ᵥ F z))‖ ≤ B from
    forall_congr' fun v ↦ caf_bdd_congr (heq v), caf_bdd_vec_iff _ hKi _ z₀ hF',
    caf_order_matrix_iff _ F z₀ hΦi (by
      rw [Matrix.det_nonsing_inv]; exact (isUnit_iff_ne_zero.mpr hΦd).ringInverse.ne_zero) hF 0]
  refine forall_congr' fun j ↦ ?_
  refine caf_order_comp_mul_nonneg_iff (fun w ↦ Rv w⁻¹ j) 0 z₀ κ u hκ hκ0 hκ' e he (hR j)
    hu.meromorphicAt ((e : ℤ) - 1) huo' (-(2 * e : ℤ)) 2 fun o ↦ ?_
  rw [caf_int_div_le_iff e he, neg_neg, Int.mul_ediv_cancel _ (by exact_mod_cast he.ne')]

/-- **The holomorphy criterion for q-forms over `s = ∞`.** -/
theorem caf_infty_qForm_iff (s l : ℂ → ℂ) (z₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, (s z)⁻¹ = ((z - z₀) * l z) ^ e)
    (Φ : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hΦ : ∀ i j, AnalyticAt ℂ (fun z ↦ Φ z i j) z₀)
    (hΦd : (Φ z₀).det ≠ 0) (Km : Matrix (Fin 4) (Fin 4) ℂ) (hK : IsUnit Km.det)
    (Ym : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (hY : ∀ᶠ z in 𝓝[≠] z₀, Ym z = Φ z * Km)
    (Qv : ℂ → Fin 4 → ℂ) (hQ : ∀ j, MeromorphicAt (fun w ↦ Qv w⁻¹ j) 0) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
        ‖(v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ j, (2 : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ Qv w⁻¹ j) 0 := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
  have hκ0 : κ z₀ = 0 := by simp [κ]
  have hκ' : deriv κ z₀ ≠ 0 := by
    have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
    rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
    rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
  obtain ⟨hua, huo⟩ := caf_deriv_param (fun z ↦ 0 + κ z ^ e) l z₀ 0 e he hl hl0
    (Eventually.of_forall fun z ↦ rfl)
  set u : ℂ → ℂ := fun z ↦ -deriv (fun y ↦ 0 + κ y ^ e) z
  have hu : AnalyticAt ℂ u z₀ := hua.neg
  have huo' : meromorphicOrderAt u z₀ = (((e : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [show u = -deriv (fun y ↦ 0 + κ y ^ e) from rfl, ← meromorphicOrderAt_neg, huo]
  set F : ℂ → Fin 4 → ℂ := fun z j ↦ κ z ^ (-(2 * e : ℤ)) * (fun w ↦ Qv w⁻¹ j) (0 + κ z ^ e) * u z
  have hF : ∀ j, MeromorphicAt (fun z ↦ F z j) z₀ := fun j ↦
    (caf_order_comp_mul (fun w ↦ Qv w⁻¹ j) 0 z₀ κ u hκ hκ0 hκ' e he (hQ j)
      hu.meromorphicAt _).1
  have hΦt : ∀ i j, AnalyticAt ℂ (fun z ↦ (Φ z)ᵀ i j) z₀ := fun i j ↦ hΦ j i
  have hF' : ∀ i, MeromorphicAt (fun z ↦ ((Φ z)ᵀ *ᵥ F z) i) z₀ := fun i ↦
    caf_meromorphic_mulVec _ _ z₀ (fun i j ↦ (hΦt i j).meromorphicAt) hF i
  have hKt : IsUnit (Kmᵀ).det := by rw [Matrix.det_transpose]; exact hK
  have heq : ∀ v : Fin 4 → ℂ, (fun z ↦ (v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z) =ᶠ[𝓝[≠] z₀]
      fun z ↦ v ⬝ᵥ (Kmᵀ *ᵥ ((Φ z)ᵀ *ᵥ F z)) := by
    intro v
    filter_upwards [hY, caf_deriv_infty s l z₀ e hl hl0 hs] with z hYz ⟨hκz, hsz, hdz⟩
    rw [hYz, Matrix.transpose_mul, hsz, hdz, ← Matrix.mulVec_mulVec]
    rw [mul_comm, ← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    congr 3
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, F, u, zero_add, κ]
    ring
  rw [show (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀,
      ‖(v ⬝ᵥ ((Ym z)ᵀ *ᵥ Qv (s z))) * deriv s z‖ ≤ B) ↔
      ∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] z₀, ‖v ⬝ᵥ (Kmᵀ *ᵥ ((Φ z)ᵀ *ᵥ F z))‖ ≤ B from
    forall_congr' fun v ↦ caf_bdd_congr (heq v), caf_bdd_vec_iff _ hKt _ z₀ hF',
    caf_order_matrix_iff _ F z₀ hΦt (by rw [Matrix.det_transpose]; exact hΦd) hF 0]
  refine forall_congr' fun j ↦ ?_
  refine caf_order_comp_mul_nonneg_iff (fun w ↦ Qv w⁻¹ j) 0 z₀ κ u hκ hκ0 hκ' e he (hQ j)
    hu.meromorphicAt ((e : ℤ) - 1) huo' (-(2 * e : ℤ)) 2 fun o ↦ ?_
  rw [caf_int_div_le_iff e he, neg_neg, Int.mul_ediv_cancel _ (by exact_mod_cast he.ne')]

end HodgeLean.Foundations.Program
