import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMotion
import HodgeLean.Foundations.Program.BraidBridgesThreeProofs

/-! # Certified marking with the ambient motion retained -/
noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- The marking retains its transport family and ambient endpoint formula.
Source: `b65x_isotopy_marking_body`; `rtc_transport_motion`. -/
theorem rtc_isotopy_marking_motion (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s)) :
    ∃ E : OnePoint ℂ ≃ₜ OnePoint ℂ,
    ∃ F : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ F (t, z))) ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, F (t, OnePoint.infty) = OnePoint.infty) ∧
      (∀ t j, F (t, (b65x_ext p 0 j : OnePoint ℂ)) =
        (b65x_ext p t j : OnePoint ℂ)) ∧
      (∀ z, F (1, z) = E z) ∧
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
      (∀ z, (h z : OnePoint ℂ) = E (b65x_mob z)) ∧ ∃ γ : Fin 13 → Path x x,
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      ∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∃ χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group,
          (∀ i, χ (b63gP_loops i) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i⟧))) ∧
          ∀ j, χ (FundamentalGroup.fromPath ⟦κ₁ j⟧) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦δ j⟧)) := by
  -- transport along the extended path
  have hQc := b65x_ext_continuous p
  obtain ⟨e, heB, heI, heQ, F, hFb, hF0, hFI, hFQ, hFe, hfam⟩ := rtc_transport_motion (b65x_ext p) hQc
    (fun t ht ↦ (b65x_ext_injective p hp t ht).1) (fun t ht ↦ (b65x_ext_injective p hp t ht).2)
    (Set.range (Fin.castAdd 4))
  have hQ0c : ∀ k : Fin 12, b65x_ext p 0 (Fin.castAdd 4 k) = b65x_rnorm p k := by
    intro k; rw [b65x_ext_cfg]; simp
  have hQ1c : ∀ k : Fin 12, b65x_ext p 1 (Fin.castAdd 4 k) = mr_marks k := by
    intro k; rw [b65x_ext_cfg, ite_eq_right (by norm_num)]
    rw [show (2 * 1 - 1 : ℝ) = 1 by norm_num, b65x_configuration_one]
  have hQ0a : ∀ k : Fin 4, b65x_ext p 0 (Fin.natAdd 12 k) = ((b65x_app k : ℝ) : ℂ) := by
    intro k; rw [b65x_ext_app]; simp
  have hQ1a : ∀ k : Fin 4, b65x_ext p 1 (Fin.natAdd 12 k) = ((b65x_app k : ℝ) : ℂ) + 3 * I := by
    intro k; rw [b65x_ext_app, ite_eq_right (by norm_num)]
  let H : OnePoint ℂ ≃ₜ OnePoint ℂ := b65x_mob.trans e
  have hH : ∀ w, H w = e (b65x_mob w) := fun w ↦ rfl
  have hH0 : H ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by rw [hH, b65x_mob_zero, heI]
  have hHp : ∀ j, H (p j : OnePoint ℂ) = (mr_marks j : OnePoint ℂ) := by
    intro j
    rw [hH, b65x_mob_coe (b65x_witness_ne_zero p hp j)]
    have := heQ (Fin.castAdd 4 j)
    rw [hQ0c, hQ1c] at this
    exact this
  have hHapp : ∀ k, H (b65x_appSrc k) = ((((b65x_app k : ℝ) : ℂ) + 3 * I : ℂ) : OnePoint ℂ) := by
    intro k
    rw [hH, b65x_mob_app]
    have := heQ (Fin.natAdd 12 k)
    rw [hQ0a, hQ1a] at this
    exact this
  have hHinv : ∀ j : Fin 13, ∀ s : unitInterval,
      H (b65b_inverseNormalization (b65b_lasso (b65x_slot j) s) : OnePoint ℂ) =
        e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := by
    intro j s
    have hreg : b65b_inverseNormalization (b65b_lasso (b65x_slot j) s) ∈ b65s_regular := by
      rw [← hδ]; exact (δ j s).2
    rw [hH, b65x_mob_invN (b65x_invN_denom hreg)]
  have hxval : x.val = b65b_inverseNormalization mr_basePoint := by
    have := hδ 0 0
    rw [(δ 0).source, Set.Icc.coe_zero, b65x_lasso_zero] at this
    exact this
  have hHx : H (x.val : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) := by
    have := hHinv 0 0
    rw [Set.Icc.coe_zero, b65x_lasso_zero, heB] at this
    rw [hxval]; exact this
  -- the homeomorphism of the punctured spheres
  have hroot : ∀ j, b65r_P 5 (p j) = 0 ∨ b65r_P (-7) (p j) = 0 := by
    intro j
    have hb := (b65x_witness_box p hp j).2.2
    have hf : b65b_boxFibre (b65x_boxInv j) = 5 ∨ b65b_boxFibre (b65x_boxInv j) = -7 := by
      generalize b65x_boxInv j = k
      fin_cases k <;> norm_num [b65b_boxFibre]
    rcases hf with hf | hf
    · rw [hf] at hb; left; exact_mod_cast hb
    · rw [hf] at hb; right; exact_mod_cast hb
  have hmem : ∀ w, w ∈ b65s_sphere ↔ H w ∈ b6t_punctured mr_base := by
    intro w
    constructor
    · intro hw ⟨k, hk⟩
      induction k using Fin.lastCases with
      | last =>
        have : H w = H ((0 : ℂ) : OnePoint ℂ) := by rw [hH0, ← hk]; rfl
        rw [H.injective this] at hw
        exact hw ⟨0, rfl, Or.inl rfl⟩
      | cast j =>
        rw [b65x_branch_cast] at hk
        rw [← hHp j] at hk
        rw [← H.injective hk] at hw
        exact hw ⟨p j, rfl, Or.inr (hroot j)⟩
    · intro hw ⟨z, hz, hzb⟩
      subst hz
      rcases b65x_witness_exhaust p hp z hzb with h0 | ⟨j, hj⟩
      · subst h0; rw [hH0] at hw; exact hw ⟨Fin.last 12, rfl⟩
      · subst hj; rw [hHp] at hw; exact hw ⟨j.castSucc, b65x_branch_cast j⟩
  let h : b65s_sphere ≃ₜ b6t_punctured mr_base := H.subtype hmem
  have hhv : ∀ w : b65s_sphere, ((h w : b6t_punctured mr_base) : OnePoint ℂ) = H w := fun w ↦ rfl
  have hhsv : ∀ w : b6t_punctured mr_base, ((h.symm w : b65s_sphere) : OnePoint ℂ) = H.symm w :=
    fun w ↦ rfl
  -- the pulled-back curves
  have hcF : ∀ i (s : unitInterval), H.symm (mr_curve i s) ∈ b65s_sphere \ (b65t_F : Set (OnePoint ℂ)) := by
    intro i s
    have hin : H (H.symm (mr_curve i s)) ∈ b6t_punctured mr_base := by
      rw [H.apply_symm_apply]
      exact (mr_curve_avoids mr_base b63gP_s₀.property i s).1
    refine ⟨(hmem _).mpr hin, fun hF ↦ ?_⟩
    have hF' : H.symm (mr_curve i s) = b65x_appSrc 0 ∨ H.symm (mr_curve i s) = b65x_appSrc 1 ∨
        H.symm (mr_curve i s) = b65x_appSrc 2 ∨ H.symm (mr_curve i s) = b65x_appSrc 3 := by
      simpa [b65t_F, b65x_appSrc] using hF
    rcases hF' with h' | h' | h' | h' <;>
    · have := congrArg H h'
      rw [H.apply_symm_apply, hHapp] at this
      exact b65x_curve_avoid_app i s _ this
  have hBF : H.symm (mr_basePoint : OnePoint ℂ) = (x.val : OnePoint ℂ) := by
    rw [← hHx, H.symm_apply_apply]
  let zF : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ))) := b65t_chart x
  have hzF : ∀ i, (⟨H.symm (mr_curve i 0), hcF i 0⟩ : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) =
      zF := by
    intro i; apply Subtype.ext
    change H.symm (mr_curve i 0) = (x.val : OnePoint ℂ)
    rw [mr_curve_zero, hBF]
  have hzF1 : ∀ i, (⟨H.symm (mr_curve i 1), hcF i 1⟩ : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) =
      zF := by
    intro i; apply Subtype.ext
    change H.symm (mr_curve i 1) = (x.val : OnePoint ℂ)
    rw [mr_curve_one, hBF]
  let pF : Fin 13 → Path zF zF := fun i ↦
    { toFun := fun s ↦ ⟨H.symm (mr_curve i s), hcF i s⟩
      continuous_toFun := (H.symm.continuous.comp ((mr_curve_continuous i).comp
        continuous_subtype_val)).subtype_mk _
      source' := hzF i
      target' := hzF1 i }
  let γ : Fin 13 → Path x x := fun i ↦ (pF i).map b65t_unchart.continuous
  have hγv : ∀ i s, ((b65s_inclusion (γ i s) : b65s_sphere) : OnePoint ℂ) = H.symm (mr_curve i s) := by
    intro i s
    exact (b65t_elim_mem (pF i s)).2
  refine ⟨e, F, hFb, hF0, hFI, hFQ, hFe, h, fun _ ↦ rfl, γ,
    fun i s ↦ ?_, fun i s ↦ ?_, fun ρ ↦ ?_⟩
  · rw [hhv, hγv, H.apply_symm_apply]
  · have hnF := (hcF i s).2
    have hv : ((γ i s).val : OnePoint ℂ) = H.symm (mr_curve i s) := hγv i s
    refine ⟨fun h3 ↦ hnF ?_, fun h1 ↦ hnF ?_, fun h2 ↦ hnF ?_, OnePoint.coe_ne_infty _⟩
    · rw [← hv, h3]; simp [b65t_F]
    · rw [← hv, h1]; simp [b65t_F]
    · rw [← hv, h2]; simp [b65t_F]
  -- the marking
  have hx0 : h.symm b63gP_basePoint = b65s_inclusion x := by
    apply Subtype.ext
    rw [hhsv]
    change H.symm (mr_basePoint : OnePoint ℂ) = (x.val : OnePoint ℂ)
    exact hBF
  obtain ⟨χ, hχ⟩ := b65x_transfer_hom h.symm b63gP_basePoint (b65s_inclusion x) hx0 ρ
  refine ⟨χ, fun i ↦ ?_, fun j ↦ ?_⟩
  · let M : Path b63gP_basePoint b63gP_basePoint := b65x_mkPath _ _ (mr_curve i ·)
      ((mr_curve_continuous _).comp continuous_subtype_val)
      (fun s ↦ (mr_curve_avoids mr_base b63gP_s₀.property i s).1)
      (mr_curve_zero _) (mr_curve_one _)
    rw [← b65x_loops_eq i M (fun s ↦ rfl), hχ]
    have hpe : (M.map h.symm.continuous).cast hx0.symm hx0.symm =
        (γ i).map b65s_inclusion.continuous := by
      apply Path.ext; funext s; apply Subtype.ext
      change H.symm (mr_curve i s) = ((b65s_inclusion (γ i s) : b65s_sphere) : OnePoint ℂ)
      rw [hγv]
    rw [hpe]; rfl
  · -- the transported lasso
    have hb : h (b65s_inclusion x) = b63gP_basePoint := by
      apply Subtype.ext; rw [hhv]; exact hHx
    let T : Path b63gP_basePoint b63gP_basePoint :=
      (((δ j).map b65s_inclusion.continuous).map h.continuous).cast hb.symm hb.symm
    have hTv : ∀ s, (T s : OnePoint ℂ) = e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := by
      intro s
      change H ((δ j s).val : OnePoint ℂ) = _
      rw [hδ, hHinv]
    let Kx : C(unitInterval × unitInterval, OnePoint ℂ) :=
      ⟨fun q ↦ K j (b65x_late q.1, q.2), (K j).continuous.comp
        ((b65x_late_continuous.comp continuous_fst).prodMk continuous_snd)⟩
    have hTκ : T.Homotopic (κ₁ j) := by
      apply hfam Kx _ _ _ _ (κ₁ j) T
      · intro s; rw [hκ₁]; change K j (1, s) = K j (b65x_late 1, s); rw [b65x_late_one]
      · intro s; rw [hTv]; change _ = e (K j (b65x_late 0, s))
        rw [b65x_late_of_le (by simp), hK0]
      · intro t; exact hKb j (b65x_late t)
      · intro t s
        refine ⟨(hKa j _ s).1, ?_⟩
        rintro _ ⟨k, rfl⟩
        by_cases ht : (t : ℝ) ≤ 1/2
        · change K j (b65x_late t, s) ≠ _
          rw [b65x_late_of_le ht, hK0]
          intro he
          exact b65x_lasso_avoid _ s ⟨s.2.1, s.2.2⟩ k _ (b65x_ext_disc p hp t ⟨t.2.1, ht⟩ k)
            (OnePoint.coe_injective he)
        · push Not at ht
          change K j (b65x_late t, s) ≠ _
          rw [b65x_ext_cfg, ite_eq_right (not_le.mpr ht)]
          have := (hKa j (b65x_late t) s).2 k
          rwa [b65x_late_of_gt ht] at this
      · intro w hw hj
        apply b65x_mem_punctured hw
        intro k
        have := hj (Fin.castAdd 4 k) ⟨k, rfl⟩
        rwa [hQ1c] at this
    have hcl : FundamentalGroup.fromPath ⟦κ₁ j⟧ = FundamentalGroup.fromPath ⟦T⟧ :=
      (congrArg FundamentalGroup.fromPath (Quotient.sound hTκ)).symm
    rw [hcl, hχ]
    have hpe : (T.map h.symm.continuous).cast hx0.symm hx0.symm =
        (δ j).map b65s_inclusion.continuous := by
      apply Path.ext; funext s; apply Subtype.ext
      change H.symm (H ((δ j s).val : OnePoint ℂ)) = _
      rw [H.symm_apply_apply]
      rfl
    rw [hpe]; rfl

end Witness

/-- Certified lasso transport with the same ambient endpoint used by the marking.
Source: `b65b_path_lasso_transport_aux`; `rtc_isotopy_marking_motion`. -/
theorem rtc_path_lasso_motion (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ E : OnePoint ℂ ≃ₜ OnePoint ℂ,
    ∃ F : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ F (t, z))) ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, F (t, OnePoint.infty) = OnePoint.infty) ∧
      (∀ t j, F (t, (b65x_ext p 0 j : OnePoint ℂ)) =
        (b65x_ext p t j : OnePoint ℂ)) ∧
      (∀ z, F (1, z) = E z) ∧
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
      (∀ z, (h z : OnePoint ℂ) = E (b65x_mob z)) ∧
    ∃ γ : Fin 13 → Path x x,
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) ∧
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      (∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i.rev⟧)) =
          b65s_word [.positive 3, .positive 2]
            (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
              (FundamentalGroup.fromPath ⟦δ j⟧))) i) := by
  obtain ⟨K, hK0, hKb, hKa⟩ := b65x_moving_lasso_aux p hp
  obtain ⟨κ₁, hκ₁⟩ := b65x_final_loops_aux p K hKb hKa
  obtain ⟨E, F, hFb, hF0, hFI, hFQ, hFe, h, hh, γ, htrace, hsrc, hmark⟩ :=
    rtc_isotopy_marking_motion p hp x δ hδ K hK0 hKb hKa κ₁ hκ₁
  refine ⟨E, F, hFb, hF0, hFI, hFQ, hFe, K, h, hh, γ, hK0, hKb, hKa, htrace, hsrc, fun ρ i ↦ ?_⟩
  obtain ⟨χ, hχγ, hχκ⟩ := hmark ρ
  rw [← hχγ, b65x_event_moves_aux p hp K hK0 hKb hKa κ₁ hκ₁ χ i]
  change b65s_word b65b_pathWord _ i = b65s_word b65b_pathWord _ i
  congr 1
  funext j
  exact hχκ j


end HodgeLean.Foundations.Program
