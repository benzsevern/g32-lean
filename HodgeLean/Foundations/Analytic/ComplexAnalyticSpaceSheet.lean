import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceLower
import HodgeLean.Foundations.AnalyticGermLyingOver

/-! # Sheets over the complement of the discriminant

Helpers prefixed `anb_`. Let `Z` be the common zero set of finitely many functions on an open
`W ⊆ ℂⁿ`, with a proper surjective projection `π` onto an open `V ⊆ ℂᴰ`, and suppose that near the
origin the points of `Z` satisfy `q(π z, ℓ z) = 0` and `Δ(π z) z = r(π z, ℓ z)` for representative
polynomials `q`, `r` and a function `Δ` not vanishing identically, with `q` having simple roots off
`Δ = 0`. Then arbitrarily near the origin there is an open `V' ⊆ ℂᴰ` and an analytic section `σ`
of `π` over `V'` with values in `Z`, near each of whose points `Z` is exactly the graph of `σ`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Polynomial

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- **Sheets.** -/
theorem anb_sheet {n D m : ℕ} (f : Fin m → (Fin n → ℂ) → ℂ) (W1 : Set (Fin n → ℂ))
    (hf : ∀ j, ContinuousOn (f j) W1) (π : (Fin n → ℂ) →L[ℂ] (Fin D → ℂ))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (Q : Polynomial (AnalyticGerm D))
    (r : Fin n → Polynomial (AnalyticGerm D)) (Δ : (Fin D → ℂ) → ℂ) (hΔa : AnalyticAt ℂ Δ 0)
    (hΔ : ¬ Δ =ᶠ[𝓝 0] 0)
    (hE1 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) → (anb_evPoly Q (π z)).eval (ℓ z) = 0)
    (hE2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) →
      ∀ i, Δ (π z) * z i = (anb_evPoly (r i) (π z)).eval (ℓ z))
    (hE3 : ∀ᶠ w in 𝓝 (0 : Fin D → ℂ), ∀ t, (anb_evPoly Q w).eval t = 0 → Δ w ≠ 0 →
      (anb_evPoly Q w).derivative.eval t ≠ 0)
    (V1 : Set (Fin D → ℂ)) (hV1 : IsOpen V1) (hV10 : (0 : Fin D → ℂ) ∈ V1)
    (prj : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} → V1) (hprj : ∀ z, (prj z).val = π z.val)
    (hproper : IsProperMap prj) (hfib : ∀ w, (prj ⁻¹' {w}).Finite)
    (hsurj : Function.Surjective prj) (hprj0 : ∀ z, (prj z).val = 0 → z.val = 0)
    (Ω : Set (Fin n → ℂ)) (hΩ : IsOpen Ω) (hΩ0 : (0 : Fin n → ℂ) ∈ Ω) (hΩW : Ω ⊆ W1) :
    ∃ (V5 : Set (Fin D → ℂ)) (σ : (Fin D → ℂ) → (Fin n → ℂ)), IsOpen V5 ∧ V5.Nonempty ∧
      AnalyticOnNhd ℂ σ V5 ∧ (∀ w ∈ V5, σ w ∈ Ω ∧ (∀ j, f j (σ w) = 0) ∧ π (σ w) = w) ∧
      ∀ w ∈ V5, ∃ Os : Set (Fin n → ℂ), IsOpen Os ∧ σ w ∈ Os ∧ ∃ Vs : Set (Fin D → ℂ),
        IsOpen Vs ∧ w ∈ Vs ∧ Vs ⊆ V5 ∧ σ '' Vs = {x | x ∈ Ω ∧ ∀ j, f j x = 0} ∩ Os := by
  classical
  -- step 0: shrink `Ω` to where the equations hold
  obtain ⟨t1, ht1, ht1o, ht10⟩ := eventually_nhds_iff.1 (hE1.and hE2)
  let Ω' := Ω ∩ t1
  have hΩ' : IsOpen Ω' := hΩ.inter ht1o
  have hΩ'0 : (0 : Fin n → ℂ) ∈ Ω' := ⟨hΩ0, ht10⟩
  have hE1' : ∀ z ∈ Ω', (∀ j, f j z = 0) → (anb_evPoly Q (π z)).eval (ℓ z) = 0 :=
    fun z hz ↦ (ht1 z hz.2).1
  have hE2' : ∀ z ∈ Ω', (∀ j, f j z = 0) →
      ∀ i, Δ (π z) * z i = (anb_evPoly (r i) (π z)).eval (ℓ z) := fun z hz ↦ (ht1 z hz.2).2
  -- step 1: the parameter neighbourhood where everything is analytic and `E3` holds
  obtain ⟨t3, ht3, ht3o, ht30⟩ := eventually_nhds_iff.1 hE3
  let Vw := V1 ∩ t3 ∩ (anb_polyDom Q ∩ (⋂ i, anb_polyDom (r i)) ∩ {w | AnalyticAt ℂ Δ w})
  have hVw : IsOpen Vw := (hV1.inter ht3o).inter (((anb_isOpen_polyDom Q).inter
    (isOpen_iInter_of_finite fun i ↦ anb_isOpen_polyDom (r i))).inter (isOpen_analyticAt ℂ Δ))
  have hVw0 : (0 : Fin D → ℂ) ∈ Vw := ⟨⟨hV10, ht30⟩, ⟨anb_zero_mem_polyDom Q,
    mem_iInter.2 fun i ↦ anb_zero_mem_polyDom (r i)⟩, hΔa⟩
  -- step 2: points over a small neighbourhood of `0` lie in `Ω'`
  obtain ⟨M, hM, hM0, hMN⟩ := anb_proper_nhds hproper (y := ⟨0, hV10⟩)
    (N := {z | z.val ∈ Ω'}) (hΩ'.preimage continuous_subtype_val) (by
      intro z hz
      have : (prj z).val = 0 := by rw [mem_preimage, mem_singleton_iff] at hz; rw [hz]
      show z.val ∈ Ω'
      rw [hprj0 z this]; exact hΩ'0)
  let M' := Subtype.val '' M ∩ Vw
  have hM' : IsOpen M' := (hV1.isOpenMap_subtype_val _ hM).inter hVw
  have hM'0 : (0 : Fin D → ℂ) ∈ M' := ⟨⟨_, hM0, rfl⟩, hVw0⟩
  have hM'Ω : ∀ z : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0}, π z.val ∈ M' → z.val ∈ Ω' := by
    intro z hz
    obtain ⟨⟨w, hw⟩, hwM, hwz⟩ := hz.1
    have : prj z = ⟨w, hw⟩ := Subtype.ext ((hprj z).trans hwz.symm)
    exact hMN (show prj z ∈ M from this ▸ hwM)
  -- step 3: a point `w₀` near `0` off the discriminant
  have hΔc : ContinuousOn Δ Vw := fun w hw ↦ hw.2.2.continuousAt.continuousWithinAt
  let V3 := M' ∩ Δ ⁻¹' {0}ᶜ
  have hV3 : IsOpen V3 :=
    (hΔc.mono fun w hw ↦ hw.2).isOpen_inter_preimage hM' isOpen_compl_singleton
  obtain ⟨w₀, hw₀M', hw₀Δ⟩ : ∃ w, w ∈ M' ∧ Δ w ≠ 0 := by
    have hfreq : ∃ᶠ w in 𝓝 (0 : Fin D → ℂ), Δ w ≠ 0 := by
      rw [Filter.Frequently]
      intro h
      apply hΔ
      filter_upwards [h] with w hw
      simpa using hw
    obtain ⟨w, hw1, hw2⟩ := (hfreq.and_eventually (hM'.mem_nhds hM'0)).exists
    exact ⟨w, hw2, hw1⟩
  have hw₀V3 : w₀ ∈ V3 := ⟨hw₀M', hw₀Δ⟩
  have hw₀Vw : w₀ ∈ Vw := hw₀M'.2
  have hw₀V1 : w₀ ∈ V1 := hw₀Vw.1.1
  let y₀ : V1 := ⟨w₀, hw₀V1⟩
  -- step 4: analytic root branches through the points over `w₀`
  have hfibπ : ∀ z ∈ prj ⁻¹' {y₀}, π z.val = w₀ := fun z hz ↦
    (hprj z).symm.trans (congrArg Subtype.val (mem_singleton_iff.1 hz))
  have hfibΩ : ∀ z ∈ prj ⁻¹' {y₀}, z.val ∈ Ω' := fun z hz ↦ hM'Ω z ((hfibπ z hz).symm ▸ hw₀M')
  have hbranch : ∀ z : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0}, ∃ (τ : (Fin D → ℂ) → ℂ)
      (U : Set ((Fin D → ℂ) × ℂ)), z ∈ prj ⁻¹' {y₀} → AnalyticAt ℂ τ w₀ ∧ τ w₀ = ℓ z.val ∧
        IsOpen U ∧ (w₀, ℓ z.val) ∈ U ∧
        ∀ u ∈ U, ((anb_evPoly Q u.1).eval u.2 = 0 ↔ τ u.1 = u.2) := by
    intro z
    by_cases hz : z ∈ prj ⁻¹' {y₀}
    · have hroot := hE1' z.val (hfibΩ z hz) z.2.2
      rw [hfibπ z hz] at hroot
      have hsimple := ht3 w₀ hw₀Vw.1.2 (ℓ z.val) hroot hw₀Δ
      obtain ⟨τ, hτa, hτ0, U, hUo, hU0, hU⟩ := anb_root_branch Q hw₀Vw.2.1.1 hroot hsimple
      exact ⟨τ, U, fun _ ↦ ⟨hτa, hτ0, hUo, hU0, hU⟩⟩
    · exact ⟨0, ∅, fun h ↦ absurd h hz⟩
  choose τ U hbr using hbranch
  let σ : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} → (Fin D → ℂ) → (Fin n → ℂ) :=
    fun z w i ↦ (anb_evPoly (r i) w).eval (τ z w) / Δ w
  have hσa : ∀ z ∈ prj ⁻¹' {y₀}, ∀ w, AnalyticAt ℂ (τ z) w → w ∈ Vw → Δ w ≠ 0 →
      AnalyticAt ℂ (σ z) w := by
    intro z _ w hτw hwVw hΔw
    refine analyticAt_pi_iff.2 fun i ↦ ?_
    have h1 : AnalyticAt ℂ (fun w ↦ (anb_evPoly (r i) w).eval (τ z w)) w :=
      (anb_evPoly_analyticAt (r i) (mem_iInter.1 hwVw.2.1.2 i) (τ z w)).comp_of_eq
        (f := fun w ↦ (w, τ z w)) (analyticAt_id.prod hτw) rfl
    exact h1.div hwVw.2.2 hΔw
  have hσ₀ : ∀ z ∈ prj ⁻¹' {y₀}, σ z w₀ = z.val := by
    intro z hz
    funext i
    have h := hE2' z.val (hfibΩ z hz) z.2.2 i
    rw [hfibπ z hz, ← (hbr z hz).2.1] at h
    exact ((eq_div_iff hw₀Δ).2 (by rw [mul_comm]; exact h)).symm
  -- step 6: points over a neighbourhood of `w₀` lie near the fibre over `w₀`
  set fib := prj ⁻¹' {y₀}
  have hπℓ : Continuous (fun y : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} ↦
      (π y.val, ℓ y.val)) :=
    (π.continuous.comp continuous_subtype_val).prodMk (ℓ.continuous.comp continuous_subtype_val)
  let N' := ⋃ z ∈ fib, {y : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} |
    (π y.val, ℓ y.val) ∈ U z}
  have hN' : IsOpen N' := isOpen_biUnion fun z hz ↦ ((hbr z hz).2.2.1).preimage hπℓ
  have hfibN' : fib ⊆ N' := fun z hz ↦ mem_biUnion hz (by
    show (π z.val, ℓ z.val) ∈ U z
    rw [hfibπ z hz]; exact (hbr z hz).2.2.2.1)
  obtain ⟨M2, hM2, hM20, hM2N⟩ := anb_proper_nhds hproper hN' hfibN'
  -- step 7: the parameter set `V4`
  let G : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} → Set (Fin D → ℂ) := fun z ↦
    (({w | AnalyticAt ℂ (τ z) w} ∩ Vw ∩ Δ ⁻¹' {0}ᶜ) ∩ (fun w ↦ (w, τ z w)) ⁻¹' U z) ∩
      σ z ⁻¹' Ω'
  have hG : ∀ z ∈ fib, IsOpen (G z) ∧ w₀ ∈ G z := by
    intro z hz
    have hA : IsOpen ({w | AnalyticAt ℂ (τ z) w} ∩ Vw ∩ Δ ⁻¹' {0}ᶜ) :=
      (hΔc.mono fun w hw ↦ hw.2).isOpen_inter_preimage ((isOpen_analyticAt ℂ _).inter hVw)
        isOpen_compl_singleton
    have hτc : ContinuousOn (fun w ↦ (w, τ z w))
        ({w | AnalyticAt ℂ (τ z) w} ∩ Vw ∩ Δ ⁻¹' {0}ᶜ) :=
      continuousOn_id.prodMk fun w hw ↦ hw.1.1.continuousAt.continuousWithinAt
    have hB := hτc.isOpen_inter_preimage hA (hbr z hz).2.2.1
    have hσc : ContinuousOn (σ z) (({w | AnalyticAt ℂ (τ z) w} ∩ Vw ∩ Δ ⁻¹' {0}ᶜ) ∩
        (fun w ↦ (w, τ z w)) ⁻¹' U z) := fun w hw ↦
      (hσa z hz w hw.1.1.1 hw.1.1.2 hw.1.2).continuousAt.continuousWithinAt
    refine ⟨hσc.isOpen_inter_preimage hB hΩ', ⟨⟨⟨(hbr z hz).1, hw₀Vw⟩, hw₀Δ⟩, ?_⟩, ?_⟩
    · show (w₀, τ z w₀) ∈ U z
      rw [(hbr z hz).2.1]; exact (hbr z hz).2.2.2.1
    · show σ z w₀ ∈ Ω'
      rw [hσ₀ z hz]; exact hfibΩ z hz
  let V4 := (Subtype.val '' M2 ∩ V3) ∩ ⋂ z ∈ fib, G z
  have hV4 : IsOpen V4 := ((hV1.isOpenMap_subtype_val _ hM2).inter hV3).inter
    ((hfib y₀).isOpen_biInter fun z hz ↦ (hG z hz).1)
  have hw₀V4 : w₀ ∈ V4 := ⟨⟨⟨y₀, hM20, rfl⟩, hw₀V3⟩, mem_iInter₂.2 fun z hz ↦ (hG z hz).2⟩
  have hV4G : ∀ z ∈ fib, V4 ⊆ G z := fun z hz w hw ↦ mem_iInter₂.1 hw.2 z hz
  have hV4V3 : V4 ⊆ V3 := fun w hw ↦ hw.1.2
  -- step 8: the closed pieces `C z` of `V4` over which the branch through `z` lies in `Z`
  let C : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0} → Set (Fin D → ℂ) := fun z ↦
    {w | (∀ j, f j (σ z w) = 0) ∧ π (σ z w) = w ∧ ℓ (σ z w) = τ z w}
  have hrel : ∀ z ∈ fib, IsOpen (V4 \ C z) := by
    intro z hz
    let Φ : (Fin D → ℂ) → (Fin m → ℂ) × (Fin D → ℂ) × ℂ := fun w ↦
      (fun j ↦ f j (σ z w), π (σ z w) - w, ℓ (σ z w) - τ z w)
    have hσc : ContinuousOn (σ z) V4 := fun w hw ↦
      (hσa z hz w (hV4G z hz hw).1.1.1.1 (hV4G z hz hw).1.1.1.2
        (hV4G z hz hw).1.1.2).continuousAt.continuousWithinAt
    have hτc : ContinuousOn (τ z) V4 := fun w hw ↦
      (hV4G z hz hw).1.1.1.1.continuousAt.continuousWithinAt
    have hσΩ : MapsTo (σ z) V4 Ω' := fun w hw ↦ (hV4G z hz hw).2
    have hΦc : ContinuousOn Φ V4 := by
      refine ContinuousOn.prodMk (continuousOn_pi.2 fun j ↦ ?_)
        (ContinuousOn.prodMk ((π.continuous.comp_continuousOn hσc).sub continuousOn_id)
          ((ℓ.continuous.comp_continuousOn hσc).sub hτc))
      exact ((hf j).mono fun x hx ↦ hΩW hx.1).comp hσc hσΩ
    have : V4 \ C z = V4 ∩ Φ ⁻¹' {0}ᶜ := by
      ext w
      simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff,
        C, Φ, mem_ofPred_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, sub_eq_zero,
        funext_iff, Pi.zero_apply]
    rw [this]
    exact hΦc.isOpen_inter_preimage hV4 isOpen_compl_singleton
  -- a point of `Z` over a parameter where `q(π y, ℓ y) = 0` lies on the branch it is near
  have hon : ∀ z ∈ fib, ∀ y : {z : Fin n → ℂ // z ∈ W1 ∧ ∀ j, f j z = 0}, y.val ∈ Ω' →
      Δ (π y.val) ≠ 0 → (π y.val, ℓ y.val) ∈ U z → τ z (π y.val) = ℓ y.val ∧
        y.val = σ z (π y.val) := by
    intro z hz y hyΩ hΔy hyU
    have h1 := ((hbr z hz).2.2.2.2 _ hyU).1 (hE1' y.val hyΩ y.2.2)
    refine ⟨h1, funext fun i ↦ ?_⟩
    have h2 := hE2' y.val hyΩ y.2.2 i
    show y.val i = (anb_evPoly (r i) (π y.val)).eval (τ z (π y.val)) / Δ (π y.val)
    rw [h1, eq_div_iff hΔy, mul_comm]
    exact h2
  -- step 9: the pieces cover `V4`
  have hcov : V4 ⊆ ⋃ z ∈ (hfib y₀).toFinset, C z := by
    intro w hw
    obtain ⟨y2, hy2M, hy2w⟩ := hw.1.1
    obtain ⟨y, hy⟩ := hsurj y2
    have hπy : π y.val = w := (hprj y).symm.trans ((congrArg Subtype.val hy).trans hy2w)
    have hyN : y ∈ N' := hM2N (show prj y ∈ M2 from hy ▸ hy2M)
    obtain ⟨z, hz, hyU⟩ := mem_iUnion₂.1 hyN
    have hyΩ : y.val ∈ Ω' := hM'Ω y (hπy ▸ (hV4V3 hw).1)
    have hΔy : Δ (π y.val) ≠ 0 := hπy ▸ (hV4V3 hw).2
    obtain ⟨h1, h2⟩ := hon z hz y hyΩ hΔy hyU
    rw [hπy] at h1 h2
    refine mem_biUnion ((hfib y₀).mem_toFinset.2 hz) ⟨fun j ↦ ?_, ?_, ?_⟩
    · rw [← h2]; exact y.2.2 j
    · rw [← h2, hπy]
    · rw [← h2, h1]
  -- step 10: one piece contains an open set
  obtain ⟨z, hzF, V5, hV5, hV5ne, hV5V4, hV5C⟩ := anb_exists_open_of_finite_cover
    (hfib y₀).toFinset C hV4 ⟨w₀, hw₀V4⟩
    (fun z hz ↦ hrel z ((hfib y₀).mem_toFinset.1 hz)) hcov
  have hz : z ∈ fib := (hfib y₀).mem_toFinset.1 hzF
  -- step 11: the sheet
  have hσV5 : AnalyticOnNhd ℂ (σ z) V5 := fun w hw ↦
    hσa z hz w (hV4G z hz (hV5V4 hw)).1.1.1.1 (hV4G z hz (hV5V4 hw)).1.1.1.2
      (hV4G z hz (hV5V4 hw)).1.1.2
  refine ⟨V5, σ z, hV5, hV5ne, hσV5, fun w hw ↦
    ⟨((hV4G z hz (hV5V4 hw)).2).1, (hV5C hw).1, (hV5C hw).2.1⟩, fun w hw ↦ ?_⟩
  let Os := Ω' ∩ (fun x ↦ (π x, ℓ x)) ⁻¹' U z ∩ π ⁻¹' V5
  have hOs : IsOpen Os := (hΩ'.inter (((hbr z hz).2.2.1).preimage
    (π.continuous.prodMk ℓ.continuous))).inter (hV5.preimage π.continuous)
  have hσw : σ z w ∈ Os := by
    refine ⟨⟨(hV4G z hz (hV5V4 hw)).2, ?_⟩, ?_⟩
    · show (π (σ z w), ℓ (σ z w)) ∈ U z
      rw [(hV5C hw).2.1, (hV5C hw).2.2]
      exact (hV4G z hz (hV5V4 hw)).1.2
    · show π (σ z w) ∈ V5
      rw [(hV5C hw).2.1]; exact hw
  refine ⟨Os, hOs, hσw, V5 ∩ σ z ⁻¹' Os, hσV5.continuousOn.isOpen_inter_preimage hV5 hOs,
    ⟨hw, hσw⟩, inter_subset_left, ?_⟩
  ext x
  constructor
  · rintro ⟨w', ⟨hw'5, hw'O⟩, rfl⟩
    exact ⟨⟨(hV4G z hz (hV5V4 hw'5)).2.1, (hV5C hw'5).1⟩, hw'O⟩
  · rintro ⟨⟨hxΩ, hx0⟩, hxO⟩
    have hxW : x ∈ W1 := hΩW hxΩ
    have hxV5 : π x ∈ V5 := hxO.2
    obtain ⟨-, h2⟩ := hon z hz ⟨x, hxW, hx0⟩ hxO.1.1 (hV4V3 (hV5V4 hxV5)).2 hxO.1.2
    exact ⟨π x, ⟨hxV5, by rw [mem_preimage, ← h2]; exact hxO⟩, h2.symm⟩

/-- **Sheets of a prime of dimension `D`.** For a prime `P` of the analytic germs with
`dim 𝒪/P = D`, given representatives of generators analytic on `U`, arbitrarily near the origin
there is an open `V ⊆ ℂᴰ` and an analytic section of a linear projection `π` over `V`, with values
in the common zeros, near each of whose points the common zeros are exactly its graph. -/
theorem anb_prime_sheet {n m D : ℕ} (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (hD : ringKrullDim (AnalyticGerm n ⧸ P) = ((D : ℕ∞) : WithBot ℕ∞))
    (g : Fin m → AnalyticGerm n) (f : Fin m → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (hgen : Ideal.span (Set.range g) = P) (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val)
    (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (Ω : Set (Fin n → ℂ)) (hΩ : IsOpen Ω) (hΩ0 : (0 : Fin n → ℂ) ∈ Ω) :
    ∃ (π : (Fin n → ℂ) →L[ℂ] (Fin D → ℂ)) (V5 : Set (Fin D → ℂ))
      (σ : (Fin D → ℂ) → (Fin n → ℂ)), IsOpen V5 ∧ V5.Nonempty ∧
      AnalyticOnNhd ℂ σ V5 ∧ (∀ w ∈ V5, σ w ∈ Ω ∧ (∀ j, f j (σ w) = 0) ∧ π (σ w) = w) ∧
      ∀ w ∈ V5, ∃ Os : Set (Fin n → ℂ), IsOpen Os ∧ σ w ∈ Os ∧ ∃ Vs : Set (Fin D → ℂ),
        IsOpen Vs ∧ w ∈ Vs ∧ Vs ⊆ V5 ∧ σ '' Vs = {x | x ∈ Ω ∧ ∀ j, f j x = 0} ∩ Os := by
  obtain ⟨d', π, θ, -, hfinite, hinj, hcomp, hdim⟩ := adim5_finite_parameters n P hP
  have hd' : d' = D := by
    have h := (adim6_parameter_dimension d').symm.trans (hdim.trans hD)
    exact_mod_cast h
  subst hd'
  obtain ⟨W1, V1, hW1, hW10, hW1U, hV1, hV10, prj, hprj, hproper, hfib, hsurj, hprj0⟩ :=
    adim7_surjective_projection n d' m P hP π θ hfinite hinj hcomp g hgen f U hU hU0 hf hrep
  let c : Fin n → AnalyticGerm n := fun i ↦ ⟨Filter.Germ.ofFun (fun z : Fin n → ℂ ↦ z i), _,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  obtain ⟨ℓ, v, Q, δ, Rr, B', C', hv, -, -, hδ, hbez, hmin, hcoord⟩ :=
    adim7_primitive_form n d' P hP π θ hfinite hinj hcomp c (fun _ ↦ rfl)
  -- the equations of the zero set near the origin
  have hE1 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) →
      (anb_evPoly Q (π z)).eval (ℓ z) = 0 := by
    obtain ⟨H, hHmk, hHval⟩ := anb_eval₂_rep (P := P) π θ hcomp Q v hv
    have hHP : H ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hHmk]; exact (hmin Q).2 dvd_rfl
    exact anb_vanish_of_mem hgen hrep hHP hHval.symm
  let dδ : AnalyticGerm n := ⟨Filter.Germ.ofFun (fun z ↦ anb_rep δ (π z)), _,
    (anb_rep_analyticAt δ).comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hθδ : θ δ = Ideal.Quotient.mk P dδ :=
    hcomp δ (anb_rep δ) (anb_rep_analyticAt δ) (anb_rep_germ δ) dδ rfl
  have hE2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) →
      ∀ i, anb_rep δ (π z) * z i = (anb_evPoly (Rr i) (π z)).eval (ℓ z) := by
    have hi : ∀ i, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) →
        anb_rep δ (π z) * z i = (anb_evPoly (Rr i) (π z)).eval (ℓ z) := by
      intro i
      obtain ⟨H, hHmk, hHval⟩ := anb_eval₂_rep (P := P) π θ hcomp (Rr i) v hv
      have hEP : dδ * c i - H ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hθδ, hHmk, hcoord i, sub_self]
      have hval : Filter.Germ.ofFun (fun z ↦ anb_rep δ (π z) * z i -
          (anb_evPoly (Rr i) (π z)).eval (ℓ z)) = (dδ * c i - H).val := by
        change _ = dδ.val * (c i).val - H.val
        rw [hHval]
        rfl
      filter_upwards [anb_vanish_of_mem hgen hrep hEP hval] with z hz h0
      exact sub_eq_zero.1 (hz h0)
    filter_upwards [Filter.eventually_all.2 hi] with z hz h0 i using hz i h0
  have hE3 : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), ∀ t, (anb_evPoly Q w).eval t = 0 →
      anb_rep δ w ≠ 0 → (anb_evPoly Q w).derivative.eval t ≠ 0 := by
    filter_upwards [anb_bezout_rep Q B' C' δ hbez] with w hw t hq hΔ hq'
    apply hΔ
    rw [← hw t, hq, hq']
    ring
  have hΔ : ¬ anb_rep δ =ᶠ[𝓝 0] 0 := by
    intro h
    apply hδ
    apply Subtype.ext
    rw [← anb_rep_germ δ]
    exact Filter.Germ.coe_eq.2 h
  have hfc : ∀ j, ContinuousOn (f j) W1 := fun j ↦ (hf j).continuousOn.mono hW1U
  obtain ⟨V5, σ, hV5, hne, hσ, hσV, hsheet⟩ := anb_sheet f W1 hfc π ℓ Q Rr (anb_rep δ)
    (anb_rep_analyticAt δ) hΔ hE1 hE2 hE3 V1 hV1 hV10 prj hprj hproper hfib hsurj hprj0
    (Ω ∩ W1) (hΩ.inter hW1) ⟨hΩ0, hW10⟩ inter_subset_right
  refine ⟨π, V5, σ, hV5, hne, hσ, fun w hw ↦ ⟨(hσV w hw).1.1, (hσV w hw).2⟩, fun w hw ↦ ?_⟩
  obtain ⟨Os, hOs, hσOs, Vs, hVs, hwVs, hVsV5, himg⟩ := hsheet w hw
  refine ⟨Os ∩ W1, hOs.inter hW1, ⟨hσOs, (hσV w hw).1.2⟩, Vs, hVs, hwVs, hVsV5, ?_⟩
  rw [himg]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

end HodgeLean.Foundations.Analytic
