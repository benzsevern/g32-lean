import HodgeLean.Foundations.Program.BraidBridgesThreeEvents
import HodgeLean.Foundations.Program.RiemannRochProofs

/-! # The product relation of the slot lassos and the event moves

Along the auxiliary path every slot lasso is carried to the explicit lasso of a mark, so the slot
lassos at time zero satisfy the product relation of the explicit loops. Along the certified path
every slot lasso except the p10 slot is carried to the explicit lasso of its mark; the class of
the p10 slot follows from the two product relations, and the two positive moves give the
explicit loops.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

/-- The transported outer loop is the explicit outer loop. -/
theorem b65x_outer_class (Q : ℝ → Fin 12 → ℂ)
    (hout : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, ‖Q t j + 11/2‖ < 10)
    (e : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hfam : ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = e (K (0, s))) → γ'.Homotopic γ)
    (hQ1 : ∀ i, ∃ j, Q 1 j = mr_marks i)
    {y : b6t_punctured mr_base} (γ γ' : Path y y)
    (hγ : ∀ s, (γ s : OnePoint ℂ) = e (b65b_lasso 0 s : OnePoint ℂ))
    (hγ' : ∀ s, (γ' s : OnePoint ℂ) = mr_curve 12 s) : γ.Homotopic γ' := by
  have hY : ∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) →
      w ∈ b6t_punctured mr_base := by
    intro w hw hj
    apply b65x_mem_punctured hw
    intro i
    obtain ⟨j, hj'⟩ := hQ1 i
    rw [← hj']; exact hj j
  let K : C(unitInterval × unitInterval, OnePoint ℂ) :=
    ⟨fun q ↦ (mr_outer q.2 : OnePoint ℂ),
      OnePoint.continuous_coe.comp (by unfold mr_outer; fun_prop)⟩
  apply hfam K _ _ _ hY γ' γ
  · intro s; rw [hγ']; rfl
  · intro s; rw [hγ]; rfl
  · intro t
    have ho0 : mr_outer 0 = mr_basePoint := by simp [mr_outer, mr_basePoint]
    have ho1 : mr_outer 1 = mr_basePoint := by rw [← b65x_lasso_one 0]; rfl
    refine ⟨?_, ?_⟩
    · change ((mr_outer ((0 : unitInterval) : ℝ)) : OnePoint ℂ) = _
      rw [Set.Icc.coe_zero, ho0]
    · change ((mr_outer ((1 : unitInterval) : ℝ)) : OnePoint ℂ) = _
      rw [Set.Icc.coe_one, ho1]
  · intro t s
    refine ⟨OnePoint.coe_ne_infty _, fun j h ↦ ?_⟩
    have h1 := OnePoint.coe_injective h
    have h2 := b65x_outer_norm s
    rw [h1] at h2
    have := hout t t.2 j
    linarith

theorem b65x_auxMark_surj (i : Fin 12) : ∃ j, b65x_auxMark j = i := by
  fin_cases i
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩,
    ⟨10, rfl⟩, ⟨8, rfl⟩, ⟨9, rfl⟩, ⟨11, rfl⟩]

theorem b65x_slot_ne_zero (j : Fin 13) (hj : j ≠ 0) : (b65x_slot j).val ≠ 0 := by
  fin_cases j <;> simp_all [b65x_slot]

theorem b65x_auxMark_slot (j : Fin 13) (hj : j ≠ 0) :
    (b65x_auxMark (b65x_colDisc (b65x_slot j) (b65x_slot_ne_zero j hj))).castSucc = j.rev := by
  fin_cases j <;> first | exact absurd rfl hj | rfl

theorem b65x_colDisc_slot (j : Fin 13) (hj : j ≠ 0) (h4 : j ≠ 4) :
    b65x_colDisc (b65x_slot j) (b65x_slot_ne_zero j hj) ≠ 10 := by
  intro h
  have := congrArg Fin.val h
  fin_cases j <;> first | exact absurd rfl hj | exact absurd rfl h4 |
    simp [b65x_colDisc, b65x_slot] at this

theorem b65x_branch_cast (k : Fin 12) :
    b6_branch mr_base k.castSucc = (mr_marks k : OnePoint ℂ) := by
  fin_cases k <;> rfl

theorem b65x_reverse_ofFn {G : Type*} (f : Fin 13 → G) :
    (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
  simp [List.ofFn_succ, Fin.rev]

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- The slot lassos at time zero satisfy the product relation, by transport along the auxiliary
path to the explicit loops. -/
theorem b65x_slot_relation
    (y0 : {w : OnePoint ℂ // w ≠ OnePoint.infty ∧ ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)})
    (hy0 : (y0 : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) (ℓ : Fin 13 → Path y0 y0)
    (hℓ : ∀ j s, (ℓ j s : OnePoint ℂ) = (b65b_lasso (b65x_slot j) s : OnePoint ℂ)) :
    (List.ofFn fun j ↦ FundamentalGroup.fromPath ⟦ℓ j⟧).prod = 1 := by
  have hQc : Continuous (b65x_aux p) := b65x_aux_continuous p
  have hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective ((b65x_aux p) t) := by
    intro t ht a b hab
    by_contra hne
    exact b65x_aux_unblocked p hp t ht a b (Ne.symm hne) 1 ⟨zero_le_one, le_rfl⟩
      (by rw [show b65x_aux p t a = b65x_aux p t b from hab]; push_cast; ring)
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, (b65x_aux p) t j ≠ mr_basePoint :=
    fun t ht j ↦ b65x_aux_ne_base p hp t ht j
  obtain ⟨e, heB, heI, heQ, hfam⟩ := b65x_transport (b65x_aux p) hQc hinj hB
  have hQ0 : (b65x_aux p) 0 = b65b_configuration p 0 := b65x_aux_zero p
  have hQ0d : ∀ j, ‖(b65x_aux p) 0 j - b65b_track 0 j‖ < b65b_radius j := by
    intro j; rw [hQ0]; exact b65x_config_disc p hp 0 ⟨le_rfl, by norm_num⟩ j
  have hQ1 : ∀ i, ∃ j, (b65x_aux p) 1 j = mr_marks i := by
    intro i
    obtain ⟨j, hj⟩ := b65x_auxMark_surj i
    exact ⟨j, by rw [b65x_aux_one, hj]⟩
  have hmem : ∀ w, (w ≠ OnePoint.infty ∧ ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)) ↔
      e w ∈ b6t_punctured mr_base := by
    intro w
    constructor
    · rintro ⟨hw, hj⟩
      apply b65x_mem_punctured
      · intro h; rw [← heI] at h; exact hw (e.injective h)
      · intro i h
        obtain ⟨j, hj'⟩ := hQ1 i
        rw [← hj', ← heQ j, hQ0] at h
        exact hj j (e.injective h)
    · intro h
      refine ⟨fun hw ↦ ?_, fun j hw ↦ ?_⟩
      · rw [hw, heI] at h; exact h ⟨Fin.last 12, rfl⟩
      · rw [hw, ← hQ0, heQ j, b65x_aux_one] at h
        exact h ⟨(b65x_auxMark j).castSucc, b65x_branch_cast _⟩
  let hh : {w : OnePoint ℂ // w ≠ OnePoint.infty ∧ ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)}
      ≃ₜ b6t_punctured mr_base := e.subtype hmem
  obtain ⟨E, hE⟩ := RiemannRochTop_homeomorph_pi1_map hh y0
  have hyh : ((hh y0 : b6t_punctured mr_base) : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) := by
    change e y0 = _; rw [hy0, heB]
  have hloop : ∀ j : Fin 13,
      mr_IsLoop mr_base (hh y0) j.rev (E (FundamentalGroup.fromPath ⟦ℓ j⟧)) := by
    intro j
    rw [hE]
    have hvals : ∀ s, (((ℓ j).map hh.continuous) s : OnePoint ℂ) =
        e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := by
      intro s; change e (ℓ j s) = _; rw [hℓ]
    let M : Path (hh y0) (hh y0) := b65x_mkPath _ (hh y0) (mr_curve j.rev ·)
      ((mr_curve_continuous _).comp continuous_subtype_val)
      (fun s ↦ (mr_curve_avoids mr_base b63gP_s₀.property j.rev s).1)
      (by rw [hyh]; exact mr_curve_zero _) (by rw [hyh]; exact mr_curve_one _)
    refine ⟨M, fun s ↦ rfl, ?_⟩
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    apply Path.Homotopic.symm
    by_cases hj : j = 0
    · subst hj
      exact b65x_outer_class (b65x_aux p) (fun t ht k ↦ b65x_aux_outer p hp t ht k) e hfam hQ1 _ M
        (fun s ↦ by rw [hvals]; rfl) (fun s ↦ rfl)
    · have hk := b65x_auxMark_slot j hj
      exact b65x_radial_class (b65x_aux p) hQc hQ0d e heB heI heQ hfam hQ1 (b65x_slot j)
        (b65x_slot_ne_zero j hj)
        (fun t ht b hb μ hμ ↦ b65x_aux_unblocked p hp t ht _ b hb μ hμ)
        (fun t ht ↦ b65x_aux_ne_base p hp t ht _) _ (b65x_aux_one p _) hyh
        ((ℓ j).map hh.continuous) M hvals (fun s ↦ by
          change mr_curve j.rev s = _; rw [hk])
  have hrel := mr_loops_product mr_base b63gP_s₀.property (hh y0)
    (fun i ↦ E (FundamentalGroup.fromPath ⟦ℓ i.rev⟧)) (fun i ↦ by
      have := hloop i.rev; rwa [Fin.rev_rev] at this)
  rw [b65x_reverse_ofFn] at hrel
  simp only [Fin.rev_rev] at hrel
  apply E.injective
  rw [map_list_prod, List.map_ofFn, map_one]
  exact hrel

end Witness

theorem b65x_loops_eq (i : Fin 13) (M : Path b63gP_basePoint b63gP_basePoint)
    (hM : ∀ s, (M s : OnePoint ℂ) = mr_curve i s) :
    FundamentalGroup.fromPath ⟦M⟧ = b63gP_loops i :=
  (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique ⟨M, hM, rfl⟩
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec

theorem b65x_prod13 {G : Type*} [Monoid G] (f : Fin 13 → G) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 * (f 7 * (f 8 *
      (f 9 * (f 10 * (f 11 * f 12))))))))))) := by
  simp [List.ofFn_succ]

theorem b65x_prod13_rev {G : Type*} [Monoid G] (f : Fin 13 → G) :
    (List.ofFn f).reverse.prod = f 12 * (f 11 * (f 10 * (f 9 * (f 8 * (f 7 * (f 6 * (f 5 *
      (f 4 * (f 3 * (f 2 * (f 1 * f 0))))))))))) := by
  simp [List.ofFn_succ]

theorem b65x_solve {G : Type*} [Group G] (a b c d e x P : G)
    (h1 : a * (b * (d * (e * (x * P)))) = 1) (h2 : a * (b * (c * (d * (e * P)))) = 1) :
    x = e⁻¹ * d⁻¹ * c * d * e := by
  have h3 : a * (b * (d * (e * (x * P)))) = a * (b * (c * (d * (e * P)))) := h1.trans h2.symm
  have h4 := mul_left_cancel (mul_left_cancel h3)
  have h5 : x * P = e⁻¹ * d⁻¹ * c * d * e * P := by
    calc x * P = e⁻¹ * (d⁻¹ * (d * (e * (x * P)))) := by group
      _ = e⁻¹ * (d⁻¹ * (c * (d * (e * P)))) := by rw [h4]
      _ = e⁻¹ * d⁻¹ * c * d * e * P := by group
  exact mul_right_cancel h5

theorem b65x_word_eval (T : Fin 13 → b4b_Group) :
    b65s_word b65b_pathWord T = fun i ↦
      if i = 2 then T 2 * T 3 * T 4 * (T 3)⁻¹ * (T 2)⁻¹
      else if i = 3 then T 2 else if i = 4 then T 3 else T i := by
  funext i
  simp only [b65s_word, b65b_pathWord, List.foldl, b65s_step, b4_braid]
  fin_cases i <;> first | (simp [Equiv.swap_apply_def]; done) | (simp [Equiv.swap_apply_def]; group)

theorem b65x_rel_transfer {X : Type*} [TopologicalSpace X] {y y' : X} (h : y = y')
    (c : Fin 13 → Path y y)
    (hrel : (List.ofFn fun j ↦ FundamentalGroup.fromPath ⟦c j⟧).prod = 1) :
    (List.ofFn fun j ↦ FundamentalGroup.fromPath ⟦(c j).cast h.symm h.symm⟧).prod = 1 := by
  subst h; simpa using hrel

section Witness2

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- The event moves: the explicit loops are the move images of the transported slot classes. -/
theorem b65x_event_moves_body
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s))
    (χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group)
    (i : Fin 13) :
    χ (b63gP_loops i.rev) =
      b65s_word b65b_pathWord (fun j ↦ χ (FundamentalGroup.fromPath ⟦κ₁ j⟧)) i := by
  have hQc : Continuous (b65b_configuration p) := b65x_configuration_continuous p
  have hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (b65b_configuration p t) :=
    fun t ht ↦ (b65x_config_injective p hp t ht).1
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, b65b_configuration p t j ≠ mr_basePoint :=
    fun t ht ↦ (b65x_config_injective p hp t ht).2
  obtain ⟨e, heB, heI, heQ, hfam⟩ := b65x_transport (b65b_configuration p) hQc hinj hB
  have hQ0d : ∀ j, ‖b65b_configuration p 0 j - b65b_track 0 j‖ < b65b_radius j :=
    fun j ↦ b65x_config_disc p hp 0 ⟨le_rfl, by norm_num⟩ j
  have hQ1 : ∀ i, ∃ j, b65b_configuration p 1 j = mr_marks i :=
    fun i ↦ ⟨i, b65x_configuration_one p i⟩
  have hY : ∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (b65b_configuration p 1 j : OnePoint ℂ)) →
      w ∈ b6t_punctured mr_base := by
    intro w hw hj
    apply b65x_mem_punctured hw
    intro i; rw [← b65x_configuration_one p i]; exact hj i
  -- the slot lassos at time zero
  let y0 : {w : OnePoint ℂ // w ≠ OnePoint.infty ∧
      ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)} :=
    ⟨(mr_basePoint : OnePoint ℂ), OnePoint.coe_ne_infty _, fun j h ↦
      (b65x_config_injective p hp 0 ⟨le_rfl, zero_le_one⟩).2 j (OnePoint.coe_injective h).symm⟩
  have hlc : ∀ c : Fin 13, Continuous fun s : unitInterval ↦ b65b_lasso c s :=
    fun c ↦ (b65x_lasso_continuous_plane c).comp continuous_subtype_val
  let ℓ : Fin 13 → Path y0 y0 := fun j ↦
    { toFun := fun s ↦ ⟨(b65b_lasso (b65x_slot j) s : OnePoint ℂ), OnePoint.coe_ne_infty _,
        fun k h ↦ b65x_lasso_avoid _ s ⟨s.2.1, s.2.2⟩ k _ (hQ0d k) (OnePoint.coe_injective h)⟩
      continuous_toFun := (OnePoint.continuous_coe.comp (hlc _)).subtype_mk _
      source' := Subtype.ext (by simp [b65x_lasso_zero, y0])
      target' := Subtype.ext (by simp [b65x_lasso_one, y0]) }
  have hrel0 := b65x_slot_relation p hp y0 rfl ℓ (fun j s ↦ rfl)
  -- transport of the relation
  have hmem : ∀ w, (w ≠ OnePoint.infty ∧ ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)) ↔
      e w ∈ b6t_punctured mr_base := by
    intro w
    constructor
    · rintro ⟨hw, hj⟩
      apply b65x_mem_punctured
      · intro h; rw [← heI] at h; exact hw (e.injective h)
      · intro i h
        rw [← b65x_configuration_one p i, ← heQ i] at h
        exact hj i (e.injective h)
    · intro h
      refine ⟨fun hw ↦ ?_, fun j hw ↦ ?_⟩
      · rw [hw, heI] at h; exact h ⟨Fin.last 12, rfl⟩
      · rw [hw, heQ j, b65x_configuration_one] at h
        exact h ⟨j.castSucc, b65x_branch_cast _⟩
  let hh : {w : OnePoint ℂ // w ≠ OnePoint.infty ∧
      ∀ j, w ≠ (b65b_configuration p 0 j : OnePoint ℂ)} ≃ₜ b6t_punctured mr_base :=
    e.subtype hmem
  obtain ⟨E, hE⟩ := RiemannRochTop_homeomorph_pi1_map hh y0
  have hrel1 : (List.ofFn fun j ↦
      FundamentalGroup.fromPath ⟦(ℓ j).map hh.continuous⟧).prod = 1 := by
    have h := congrArg E hrel0
    rw [map_list_prod, List.map_ofFn, map_one] at h
    simpa only [Function.comp_def, hE] using h
  have hb : hh y0 = b63gP_basePoint := Subtype.ext (by change e _ = _; rw [heB]; rfl)
  have hrel2 := b65x_rel_transfer hb (fun j ↦ (ℓ j).map hh.continuous) hrel1
  have htl : ∀ j s, ((((ℓ j).map hh.continuous).cast hb.symm hb.symm) s : OnePoint ℂ) =
      e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := fun j s ↦ rfl
  have hκ : ∀ j, FundamentalGroup.fromPath ⟦κ₁ j⟧ =
      FundamentalGroup.fromPath ⟦((ℓ j).map hh.continuous).cast hb.symm hb.symm⟧ := by
    intro j
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    apply Path.Homotopic.symm
    exact hfam (K j) (hKb j) (hKa j) _ hY (κ₁ j) _ (hκ₁ j) (fun s ↦ by rw [htl, hK0])
  have hR1 : (List.ofFn fun j ↦ FundamentalGroup.fromPath ⟦κ₁ j⟧).prod = 1 := by
    simpa only [hκ] using hrel2
  -- classes of the unblocked slots
  have hcls : ∀ j, j ≠ 4 → ∀ m : Fin 13, (j = 0 → m = 12) →
      (∀ hj : j ≠ 0, m = (b65x_colDisc (b65x_slot j) (b65x_slot_ne_zero j hj)).castSucc) →
      FundamentalGroup.fromPath ⟦κ₁ j⟧ = b63gP_loops m := by
    intro j h4 m hm0 hm
    rw [hκ]
    let M : Path b63gP_basePoint b63gP_basePoint := b65x_mkPath _ _ (mr_curve m ·)
      ((mr_curve_continuous _).comp continuous_subtype_val)
      (fun s ↦ (mr_curve_avoids mr_base b63gP_s₀.property m s).1)
      (mr_curve_zero _) (mr_curve_one _)
    rw [← b65x_loops_eq m M (fun s ↦ rfl)]
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    by_cases hj : j = 0
    · subst hj
      have hm' := hm0 rfl
      subst hm'
      exact b65x_outer_class _ (fun t ht k ↦ b65x_main_outer p hp t ht k) e hfam hQ1 _ M
        (fun s ↦ by rw [htl]; rfl) (fun s ↦ rfl)
    · have hmj := hm hj
      exact b65x_radial_class _ hQc hQ0d e heB heI heQ hfam hQ1 (b65x_slot j)
        (b65x_slot_ne_zero j hj)
        (fun t ht b hb' μ hμ ↦
          b65x_main_unblocked p hp _ (b65x_colDisc_slot j hj h4) t ht b hb' μ hμ)
        (fun t ht ↦ hB t ht _) _ (b65x_configuration_one p _) rfl _ M (htl j)
        (fun s ↦ by change mr_curve m s = _; rw [hmj])
  have hX : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 4 →
      FundamentalGroup.fromPath ⟦κ₁ j⟧ = b63gP_loops j.rev := by
    intro j h2 h3 h4
    apply hcls j h4 _ (fun h ↦ by subst h; rfl)
    intro hj
    fin_cases j <;> first | exact absurd rfl hj | exact absurd rfl h2 | exact absurd rfl h3 |
      exact absurd rfl h4 | rfl
  have hX2 : FundamentalGroup.fromPath ⟦κ₁ 2⟧ = b63gP_loops 9 :=
    hcls 2 (by decide) 9 (by decide) (fun _ ↦ rfl)
  have hX3 : FundamentalGroup.fromPath ⟦κ₁ 3⟧ = b63gP_loops 8 :=
    hcls 3 (by decide) 8 (by decide) (fun _ ↦ rfl)
  -- the explicit relation and the p10 slot
  have hR2 := mr_loops_product mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops
    (fun i ↦ (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec)
  rw [b65x_prod13_rev] at hR2
  rw [b65x_prod13] at hR1
  have e0 : FundamentalGroup.fromPath ⟦κ₁ 0⟧ = b63gP_loops 12 := hX 0 (by decide) (by decide) (by decide)
  have e1 : FundamentalGroup.fromPath ⟦κ₁ 1⟧ = b63gP_loops 11 := hX 1 (by decide) (by decide) (by decide)
  have e5 : FundamentalGroup.fromPath ⟦κ₁ 5⟧ = b63gP_loops 7 := hX 5 (by decide) (by decide) (by decide)
  have e6 : FundamentalGroup.fromPath ⟦κ₁ 6⟧ = b63gP_loops 6 := hX 6 (by decide) (by decide) (by decide)
  have e7 : FundamentalGroup.fromPath ⟦κ₁ 7⟧ = b63gP_loops 5 := hX 7 (by decide) (by decide) (by decide)
  have e8 : FundamentalGroup.fromPath ⟦κ₁ 8⟧ = b63gP_loops 4 := hX 8 (by decide) (by decide) (by decide)
  have e9 : FundamentalGroup.fromPath ⟦κ₁ 9⟧ = b63gP_loops 3 := hX 9 (by decide) (by decide) (by decide)
  have e10 : FundamentalGroup.fromPath ⟦κ₁ 10⟧ = b63gP_loops 2 := hX 10 (by decide) (by decide) (by decide)
  have e11 : FundamentalGroup.fromPath ⟦κ₁ 11⟧ = b63gP_loops 1 := hX 11 (by decide) (by decide) (by decide)
  have e12 : FundamentalGroup.fromPath ⟦κ₁ 12⟧ = b63gP_loops 0 := hX 12 (by decide) (by decide) (by decide)
  rw [e0, e1, hX2, hX3, e5, e6, e7, e8, e9, e10, e11, e12] at hR1
  have hX4 := b65x_solve _ _ _ _ _ _ _ hR1 hR2
  rw [b65x_word_eval]
  fin_cases i
  · exact (show χ (b63gP_loops 12) = χ (FundamentalGroup.fromPath ⟦κ₁ 0⟧) by rw [e0])
  · exact (show χ (b63gP_loops 11) = χ (FundamentalGroup.fromPath ⟦κ₁ 1⟧) by rw [e1])
  · show χ (b63gP_loops 10) = χ (FundamentalGroup.fromPath ⟦κ₁ 2⟧) *
      χ (FundamentalGroup.fromPath ⟦κ₁ 3⟧) * χ (FundamentalGroup.fromPath ⟦κ₁ 4⟧) *
      (χ (FundamentalGroup.fromPath ⟦κ₁ 3⟧))⁻¹ * (χ (FundamentalGroup.fromPath ⟦κ₁ 2⟧))⁻¹
    rw [hX2, hX3, hX4]
    simp only [map_mul, map_inv]
    group
  · exact (show χ (b63gP_loops 9) = χ (FundamentalGroup.fromPath ⟦κ₁ 2⟧) by rw [hX2])
  · exact (show χ (b63gP_loops 8) = χ (FundamentalGroup.fromPath ⟦κ₁ 3⟧) by rw [hX3])
  · exact (show χ (b63gP_loops 7) = χ (FundamentalGroup.fromPath ⟦κ₁ 5⟧) by rw [e5])
  · exact (show χ (b63gP_loops 6) = χ (FundamentalGroup.fromPath ⟦κ₁ 6⟧) by rw [e6])
  · exact (show χ (b63gP_loops 5) = χ (FundamentalGroup.fromPath ⟦κ₁ 7⟧) by rw [e7])
  · exact (show χ (b63gP_loops 4) = χ (FundamentalGroup.fromPath ⟦κ₁ 8⟧) by rw [e8])
  · exact (show χ (b63gP_loops 3) = χ (FundamentalGroup.fromPath ⟦κ₁ 9⟧) by rw [e9])
  · exact (show χ (b63gP_loops 2) = χ (FundamentalGroup.fromPath ⟦κ₁ 10⟧) by rw [e10])
  · exact (show χ (b63gP_loops 1) = χ (FundamentalGroup.fromPath ⟦κ₁ 11⟧) by rw [e11])
  · exact (show χ (b63gP_loops 0) = χ (FundamentalGroup.fromPath ⟦κ₁ 12⟧) by rw [e12])

end Witness2

end HodgeLean.Foundations.Program
