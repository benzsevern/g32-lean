import HodgeLean.Foundations.Program.ComponentTransportNormalizedDefs

/-! # Proof obligations for the normalized certificate path -/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65v_letter_last (i : Fin 12) (hi : i ≠ 0) :
    (Fin.revPerm * b65u_movePerm [.positive i] * Fin.revPerm : Equiv.Perm (Fin 13)) 12 = 12 := by
  revert hi
  revert i
  decide +kernel

theorem b65v_letter_cast (i : Fin 12) (hi : i ≠ 0) (k : Fin 12) :
    (Fin.revPerm * b65u_movePerm [.positive i] * Fin.revPerm : Equiv.Perm (Fin 13)) k.castSucc =
      (Equiv.swap (⟨11 - i.val, by omega⟩ : Fin 11).castSucc
        (⟨11 - i.val, by omega⟩ : Fin 11).succ k).castSucc := by
  revert k
  revert hi
  revert i
  decide +kernel

theorem b65v_positive (i : Fin 12) (hi : i ≠ 0) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 13, H 1 (b6_branch mr_base k) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm [.positive i] * Fin.revPerm : Equiv.Perm (Fin 13)) k)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word [.positive i] (fun i ↦ ρ (b66h_loop i)) k := by
  obtain ⟨ε, hε, H, hHc, hH0, hHI, hHB, hHQ, h, hh, hb, hact⟩ := b66h_half_twist_body i hi
  refine ⟨H, hHc, hH0, hHI, hHB, (fun k ↦ ?_), h, hh, hb, fun ρ k ↦ ?_⟩
  · induction k using Fin.lastCases with
    | last =>
      rw [show (Fin.last 12 : Fin 13) = 12 from rfl, b65v_letter_last i hi]
      exact hHI 1
    | cast k =>
      rw [b65x_branch_cast, hHQ 1 k, Set.Icc.coe_one,
        (b66h_track_endpoints_body _ ε hε).2, b65v_letter_cast i hi k,
        b65x_branch_cast]
      rfl
  · rw [hact k, b66h_braid_map ρ i]
    rfl

theorem b65v_negative (i : Fin 12) (hi : i ≠ 0) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 13, H 1 (b6_branch mr_base k) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm [.negative i] * Fin.revPerm : Equiv.Perm (Fin 13)) k)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word [.negative i] (fun i ↦ ρ (b66h_loop i)) k := by
  obtain ⟨ε, hε, H, hHc, hH0, hHI, hHB, hHQ, h, hh, hb, hact⟩ := b66h_half_twist_body i hi
  set j : Fin 11 := ⟨11 - i.val, by omega⟩
  -- the inverse isotopy
  let F : unitInterval × OnePoint ℂ → unitInterval × OnePoint ℂ := fun q ↦ (q.1, H q.1 q.2)
  have hFc : Continuous F := continuous_fst.prodMk hHc
  have hFb : Function.Bijective F := by
    constructor
    · rintro ⟨t, a⟩ ⟨t', b⟩ hab
      simp only [F, Prod.mk.injEq] at hab
      obtain ⟨rfl, h2⟩ := hab
      rw [(H t).injective h2]
    · rintro ⟨t, b⟩
      exact ⟨(t, (H t).symm b), by simp [F]⟩
  let E : unitInterval × OnePoint ℂ ≃ₜ unitInterval × OnePoint ℂ :=
    hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hFb)
  have hEs : ∀ t w, E.symm (t, w) = (t, (H t).symm w) := by
    intro t w
    apply E.injective
    rw [E.apply_symm_apply]
    change (t, w) = F (t, (H t).symm w)
    simp [F]
  have hHs : (fun q : unitInterval × OnePoint ℂ ↦ (H q.1).symm q.2) = fun q ↦ (E.symm q).2 := by
    funext q; rw [hEs]
  have hsw : ∀ k, H 1 (mr_marks k : OnePoint ℂ) =
      (mr_marks (Equiv.swap j.castSucc j.succ k) : OnePoint ℂ) := by
    intro k
    rw [hHQ 1 k, Set.Icc.coe_one, (b66h_track_endpoints_body _ ε hε).2]
    rfl
  have hbs : h.symm b63gP_basePoint = b63gP_basePoint := by
    rw [Homeomorph.symm_apply_eq, hb]
  refine ⟨fun t ↦ (H t).symm, ?_, ?_, fun t ↦ ?_, fun t ↦ ?_,
    (fun k ↦ ?_), h.symm, fun z ↦ ?_, hbs, fun ρ k ↦ ?_⟩
  · rw [hHs]; exact continuous_snd.comp E.symm.continuous
  · show (H 0).symm = _
    rw [hH0]; rfl
  · rw [Homeomorph.symm_apply_eq, hHI]
  · rw [Homeomorph.symm_apply_eq, hHB]
  · change (H 1).symm (b6_branch mr_base k) = b6_branch mr_base
      ((Fin.revPerm * b65u_movePerm [.positive i] * Fin.revPerm : Equiv.Perm (Fin 13)) k)
    induction k using Fin.lastCases with
    | last =>
      rw [show (Fin.last 12 : Fin 13) = 12 from rfl, b65v_letter_last i hi]
      change (H 1).symm OnePoint.infty = OnePoint.infty
      rw [Homeomorph.symm_apply_eq, hHI]
    | cast k =>
      rw [b65x_branch_cast, b65v_letter_cast i hi k, b65x_branch_cast,
        Homeomorph.symm_apply_eq, hsw, Equiv.swap_apply_self]
  · show _ = (H 1).symm _
    rw [Homeomorph.eq_symm_apply, ← hh, Homeomorph.apply_symm_apply]
  · -- the inverse move
    set L := b66h_loop
    have hΨ : ∀ m, b66h_opMap h hb (L m) = b4_braid i.castSucc i.succ L m := hact
    have hinj : Function.Injective (b66h_opMap h hb) := by
      intro x y hxy
      have hl : ∀ x, b66h_opMap h.symm hbs (b66h_opMap h hb x) = x := by
        intro x
        rw [b66h_opMap_apply, b66h_opMap_apply, MulOpposite.unop_op,
          ← b66h_mapOfEq_comp h h.symm (Homeomorph.refl _) hb hbs rfl
            (fun z ↦ (h.symm_apply_apply z).symm)]
        exact (congrArg MulOpposite.op (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl)
          (MulOpposite.unop x))).trans (MulOpposite.op_unop x)
      rw [← hl x, hxy, hl y]
    have hr : ∀ x, b66h_opMap h hb (b66h_opMap h.symm hbs x) = x := by
      intro x
      rw [b66h_opMap_apply, b66h_opMap_apply, MulOpposite.unop_op,
        ← b66h_mapOfEq_comp h.symm h (Homeomorph.refl _) hbs hb rfl
          (fun z ↦ (h.apply_symm_apply z).symm)]
      exact (congrArg MulOpposite.op (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl)
        (MulOpposite.unop x))).trans (MulOpposite.op_unop x)
    have hN : b66h_opMap h.symm hbs (L k) = b66h_negStep i L k := by
      apply hinj
      rw [hr, b66h_negStep_map, show (fun m ↦ b66h_opMap h hb (L m)) =
        b4_braid i.castSucc i.succ L from funext hΨ, b66h_negStep_braid]
    change ρ (b66h_opMap h.symm hbs (L k)) = _
    rw [hN, b66h_negStep_map]
    rfl

theorem b65v_realize (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 13, H 1 (b6_branch mr_base k) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm w * Fin.revPerm : Equiv.Perm (Fin 13)) k)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word w (fun i ↦ ρ (b66h_loop i)) k := by
  induction w with
  | nil =>
    refine ⟨fun _ ↦ Homeomorph.refl _, continuous_snd, rfl, fun _ ↦ rfl,
      fun _ ↦ rfl, ?_, Homeomorph.refl _, fun _ ↦ rfl, rfl, fun ρ k ↦ ?_⟩
    · intro k
      simp [b65u_movePerm]
    · exact congrArg (fun x ↦ ρ (MulOpposite.op x))
        (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl)
          (MulOpposite.unop (b66h_loop k)))
  | cons m w ih =>
    have hm := hw m List.mem_cons_self
    have hletter :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 13, H 1 (b6_branch mr_base k) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm [m] * Fin.revPerm : Equiv.Perm (Fin 13)) k)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word [m] (fun i ↦ ρ (b66h_loop i)) k := by
      obtain ⟨i, hi, rfl | rfl⟩ := hm
      · exact b65v_positive i hi
      · exact b65v_negative i hi
    obtain ⟨H1, hHc1, hH01, hHI1, hHB1, hσ1, h1, hh1, hb1, hact1⟩ := hletter
    obtain ⟨H2, hHc2, hH02, hHI2, hHB2, hσ2, h2, hh2, hb2, hact2⟩ :=
      ih (fun m' hm' ↦ hw m' (List.mem_cons_of_mem _ hm'))
    have hb : (h2.trans h1) b63gP_basePoint = b63gP_basePoint := by
      rw [Homeomorph.trans_apply, hb2, hb1]
    refine ⟨fun t ↦ (H2 t).trans (H1 t), hHc1.comp (continuous_fst.prodMk hHc2), ?_,
      fun t ↦ ?_, fun t ↦ ?_, fun k ↦ ?_, h2.trans h1, fun z ↦ ?_, hb,
      fun ρ k ↦ ?_⟩
    · show (H2 0).trans (H1 0) = _
      rw [hH01, hH02]; rfl
    · simp [hHI1, hHI2]
    · simp [hHB1, hHB2]
    · change H1 1 (H2 1 _) = _
      rw [hσ2, hσ1]
      congr 1
      simp [b65u_movePerm, mul_assoc]
    · simp [hh1, hh2]
    · rw [b66h_mapOfEq_comp h2 h1 _ hb2 hb1 hb (fun z ↦ rfl)]
      have ht := hact2 (ρ.comp (b66h_opMap h1 hb1)) k
      simp only [MonoidHom.comp_apply, b66h_opMap_apply, MulOpposite.unop_op] at ht
      rw [ht]
      have hT : (fun i ↦ ρ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨h1, h1.continuous⟩ hb1
          (MulOpposite.unop (b66h_loop i))))) = b65s_step m (fun i ↦ ρ (b66h_loop i)) := by
        funext i; exact hact1 ρ i
      rw [hT]
      rfl

theorem b65v_word_endpoint_aux (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 12, H 1 (mr_marks k : OnePoint ℂ) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm w * Fin.revPerm : Equiv.Perm (Fin 13)) k.castSucc)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word w (fun i ↦ ρ (b66h_loop i)) k := by
  obtain ⟨H, hHc, hH0, hHI, hHB, hσ, h, hh, hb, hact⟩ := b65v_realize w hw
  exact ⟨H, hHc, hH0, hHI, hHB, fun k ↦ by
    rw [← b65x_branch_cast]; exact hσ k.castSucc, h, hh, hb, hact⟩

theorem b65v_certificate_endpoint_aux
    (ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group)
    (hρ : ∀ i, ρ (b66h_loop i) = b65s_columnRoot i) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 12, H 1 (mr_marks k : OnePoint ℂ) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm b65b_word * Fin.revPerm : Equiv.Perm (Fin 13)) k.castSucc)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ i, ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop i)))) =
            b4_conjTuple (b4b_generators 1)⁻¹ b65b_final i := by
  obtain ⟨H, hHc, hH0, hHI, hHB, hσ, h, hh, hb, hact⟩ :=
    b65v_word_endpoint_aux b65b_word b66h_word_letters
  refine ⟨H, hHc, hH0, hHI, hHB, hσ, h, hh, hb, fun i ↦ ?_⟩
  rw [hact ρ i, show (fun i ↦ ρ (b66h_loop i)) = b65s_columnRoot from funext hρ,
    b65b_replay.1]

theorem b65v_endpoint_word_aux :
    Fin.revPerm * b65u_movePerm b65b_word * Fin.revPerm = b65u_endpointPerm ∧
      b65u_endpointPerm.symm 10 = 8 ∧ b65u_endpointPerm.symm 11 = 10 ∧
      b65u_endpointPerm 12 = 12 := by
  decide +kernel

theorem b65v_affine_contMDiff (a b : ℂ) (ha : a ≠ 0)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ∀ z : ℂ, M z = ((a * z + b : ℂ) : OnePoint ℂ))
    (hMinf : M OnePoint.infty = OnePoint.infty) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M := by
  have h0 : b4cov_chart0 ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ) :=
    IsManifold.chart_mem_maximalAtlas ((0 : ℂ) : OnePoint ℂ)
  intro p
  induction p using OnePoint.rec with
  | coe z =>
    have hz : (z : OnePoint ℂ) ∈ b4cov_chart0.source := by
      rw [b4cov_chart0_source]; exact Set.mem_range_self z
    have hd := (b4cov_coe_contMDiff.contMDiffAt
      (x := a * b4cov_chart0 (z : OnePoint ℂ) + b)).comp (z : OnePoint ℂ)
      ((contMDiffAt_const.mul (contMDiffAt_of_mem_maximalAtlas h0 hz)).add contMDiffAt_const)
    apply hd.congr_of_eventuallyEq
    filter_upwards [b4cov_chart0.open_source.mem_nhds hz] with y hy
    rw [b4cov_chart0_source] at hy
    obtain ⟨w, rfl⟩ := hy
    rw [hM]
    change ((a * w + b : ℂ) : OnePoint ℂ) =
      ((a * b4cov_chart0 (w : OnePoint ℂ) + b : ℂ) : OnePoint ℂ)
    rw [b4cov_chart0_coe]
  | infty =>
    have hq : ContDiffAt ℂ ω (fun z : ℂ ↦ z / (a + b * z)) 0 :=
      contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (by simpa using ha)
    have heq : (b4cov_chartInf ∘ M ∘ b4cov_chartInf.symm) =ᶠ[𝓝 (0 : ℂ)]
        (fun z : ℂ ↦ z / (a + b * z)) := by
      have hne : ∀ᶠ z : ℂ in 𝓝 0, a + b * z ≠ 0 :=
        (by fun_prop : Continuous (fun z : ℂ ↦ a + b * z)).continuousAt.preimage_mem_nhds
          (isOpen_ne.mem_nhds (by simpa using ha))
      filter_upwards [hne] with z hz
      by_cases hz0 : z = 0
      · subst z
        simp [Function.comp_def, b4cov_chartInf_symm, b4cov_chartInf_apply,
          b4cov_sphInv_zero, hMinf, b4cov_chart0_coe, b4cov_sphInv_infty]
      · have hza : a * z⁻¹ + b ≠ 0 := by
          intro h
          apply hz
          calc
            a + b * z = (a * z⁻¹ + b) * z := by field_simp <;> ring
            _ = 0 := by rw [h, zero_mul]
        simp only [Function.comp_apply, b4cov_chartInf_symm, b4cov_sphInv_coe hz0]
        rw [hM, b4cov_chartInf_apply, b4cov_sphInv_coe hza, b4cov_chart0_coe]
        field_simp
    have hd := hq.congr_of_eventuallyEq heq
    rw [contMDiffAt_iff]
    refine ⟨M.continuous.continuousAt, ?_⟩
    simp only [hMinf]
    change ContDiffWithinAt ℂ ω
      (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : OnePoint ℂ) ∘ M ∘
        (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : OnePoint ℂ)).symm)
      (Set.range (𝓘(ℂ, ℂ)))
      (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : OnePoint ℂ) OnePoint.infty)
    simpa only [extChartAt, b4cov_chartAt_infty, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, id_eq,
      b4cov_chartInf_apply, b4cov_sphInv_infty, b4cov_chart0_coe] using hd.contDiffWithinAt

theorem b65v_relabel_normalization_aux (p : Fin 12 → ℂ) (hc : b65z_centre p ∈ b6_chart)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMz : ∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ))
    (hMinf : M OnePoint.infty = OnePoint.infty) :
    b65v_relabelCentre p ∈ b6_chart ∧
      (∀ j, M (b6_branch (b65v_relabelCentre p) (b65u_endpointPerm j)) =
        b6_branch (b65z_centre p) j) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M ∧ ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm ∧
      M '' b6t_punctured (b65v_relabelCentre p) = b6t_punctured (b65z_centre p) := by
  have h8 : b65z_centre p 8 ≠ 0 := by
    intro hz
    have he : b6_branch (b65z_centre p) 8 = b6_branch (b65z_centre p) 10 := by
      change ((b65z_centre p 8 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      exact congrArg (fun z : ℂ ↦ (z : OnePoint ℂ)) hz
    have hbad := hc he
    norm_num at hbad
  have hτ : ∀ j : Fin 13, b65u_endpointPerm j =
      ![4, 1, 0, 9, 2, 7, 3, 6, 10, 5, 11, 8, 12] j := by decide +kernel
  have hτinv : ∀ j : Fin 13, b65u_endpointPerm.symm j =
      ![2, 1, 4, 6, 0, 9, 7, 5, 11, 3, 8, 10, 12] j := by decide +kernel
  have hlabels : ∀ j, M (b6_branch (b65v_relabelCentre p) (b65u_endpointPerm j)) =
      b6_branch (b65z_centre p) j := by
    intro j
    simp only [hτ, b6_branch, b65v_relabelCentre, hτinv]
    fin_cases j
    · change M (((1 - (b65z_centre p 0) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 0 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 1) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 1 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 2) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 2 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 3) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 3 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 4) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 4 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 5) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 5 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 6) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 6 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 7) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 7 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((0) : ℂ) : OnePoint ℂ) = ((b65z_centre p 8 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (b65z_centre p 9) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((b65z_centre p 9 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1) : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · change M (((1 - (1) / b65z_centre p 8) : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ)
      rw [hMz]
      congr 1
      field_simp
      <;> ring
    · exact hMinf
  have hchart : b65v_relabelCentre p ∈ b6_chart := by
    intro i j hij
    apply b65u_endpointPerm.symm.injective
    apply hc
    rw [← hlabels (b65u_endpointPerm.symm i), ← hlabels (b65u_endpointPerm.symm j)]
    simpa only [Equiv.apply_symm_apply] using congrArg M hij
  have hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M :=
    b65v_affine_contMDiff (-b65z_centre p 8) (b65z_centre p 8) (neg_ne_zero.mpr h8)
      M (fun z ↦ by rw [hMz]; congr 1; ring) hMinf
  have hMs : ∀ z : ℂ, M.symm z =
      (((-b65z_centre p 8)⁻¹ * z + 1 : ℂ) : OnePoint ℂ) := by
    intro z
    apply M.injective
    rw [M.apply_symm_apply, hMz]
    congr 1
    field_simp
    ring
  have hMinfs : M.symm OnePoint.infty = OnePoint.infty := by
    rw [Homeomorph.symm_apply_eq, hMinf]
  refine ⟨hchart, hlabels, hM,
    b65v_affine_contMDiff _ _ (inv_ne_zero (neg_ne_zero.mpr h8)) M.symm hMs hMinfs, ?_⟩
  rw [b6t_punctured, b6t_punctured, Set.image_compl_eq M.bijective]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨b65u_endpointPerm.symm j, by simpa using (hlabels (b65u_endpointPerm.symm j)).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨b65u_endpointPerm j, rfl⟩, hlabels j⟩


theorem b65v_radial_marks (c : ℕ → Fin 10 → ℂ) (N : ℕ)
    (hc₀ : c 0 ∈ b6_chart)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k)) :
    ∀ j, b65y_radial c N (b6_branch (c 0) j) = b6_branch (c N) j := by
  have hchart : ∀ k ≤ N, c k ∈ b6_chart := by
    intro k hk
    induction k with
    | zero => exact hc₀
    | succ k ih =>
      exact (b6t_polydisc_neighbourhood (c k) (ih (by omega))).2.2.2 (hc k (by omega))
  induction N with
  | zero => intro j; rfl
  | succ N ih =>
    intro j
    change b6t_sphere (c N) (c (N + 1))
      (b65y_radial c N (b6_branch (c 0) j)) = _
    rw [ih (fun k hk ↦ hc k (by omega)) (fun k hk ↦ hchart k (by omega))]
    exact b6t_marks (c N) (hchart N (by omega)) (c (N + 1)) (hc N (by omega)) j

theorem b65v_radial_endpoint_labels (p : Fin 12 → ℂ) (hp : b65z_centre p ∈ b6_chart)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMz : ∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ))
    (hMinf : M OnePoint.infty = OnePoint.infty)
    (c : ℕ → Fin 10 → ℂ) (N : ℕ) (h₀ : c 0 = mr_base)
    (h₁ : c N = b65v_relabelCentre p)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k)) :
    ∀ j, M (b65y_radial c N (b6_branch mr_base (b65u_endpointPerm j))) =
      b6_branch (b65z_centre p) j := by
  have hchart : c 0 ∈ b6_chart := h₀ ▸ mr_base_mem_chart
  intro j
  rw [← h₀, b65v_radial_marks c N hchart hc, h₁]
  exact (b65v_relabel_normalization_aux p hp M hMz hMinf).2.1 j

theorem b65v_escape_step_bound (γ : C(unitInterval, Fin 10 → ℂ)) (t₁ : ℝ)
    (hescape : ∀ t : unitInterval, t₁ ≤ (t : ℝ) →
      γ t ∉ b6t_polydisc (γ 0))
    (N : ℕ) (hN : 0 < N)
    (hc : ∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) :
    (1 : ℝ) / N < t₁ := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htime : (1 : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hN'⟩
  have hfirst := hc 0 hN
  simp only [b65y_sample, Nat.cast_zero, zero_div, Set.projIcc_left, zero_add,
    Nat.cast_one] at hfirst
  by_contra hle
  apply hescape (Set.projIcc 0 1 zero_le_one ((1 : ℝ) / N)) _ hfirst
  rw [Set.projIcc_of_mem _ htime]
  exact le_of_not_gt hle

theorem b65v_braid_negStep {G : Type*} [Group G] (i : Fin 12) (T : Fin 13 → G) :
    b4_braid i.castSucc i.succ (b66h_negStep i T) = T := by
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  funext k
  unfold b66h_negStep b4_braid
  by_cases hk : k = i.castSucc
  · subst hk
    simp [Function.update_of_ne hne, Function.update_self, Equiv.swap_apply_left]
    group
  · rw [Function.update_of_ne hk, Function.comp_apply]
    by_cases hk' : k = i.succ
    · subst hk'
      simp [Equiv.swap_apply_right, Function.update_of_ne hne]
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk', Function.update_of_ne hk']
      simp [Equiv.swap_apply_of_ne_of_ne hk hk']

theorem b65v_word_injective (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    Function.Injective (b65s_word w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons m w ih =>
    intro T U h
    have hs : b65s_step m T = b65s_step m U :=
      ih (fun m' hm' ↦ hw m' (List.mem_cons_of_mem _ hm')) h
    obtain ⟨i, _, rfl | rfl⟩ := hw m List.mem_cons_self
    · have ht := congrArg (b66h_negStep i) hs
      simpa only [b65s_step, b66h_negStep_braid] using ht
    · have ht := congrArg (b4_braid i.castSucc i.succ) hs
      change b4_braid _ _ (b66h_negStep i T) = b4_braid _ _ (b66h_negStep i U) at ht
      simpa only [b65v_braid_negStep] using ht

theorem b65v_word_conj (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i))
    (a : b4b_Group) (T : Fin 13 → b4b_Group) :
    b65s_word w (b4_conjTuple a T) = b4_conjTuple a (b65s_word w T) := by
  induction w generalizing T with
  | nil => rfl
  | cons m w ih =>
    change b65s_word w (b65s_step m (b4_conjTuple a T)) = _
    have hs : b65s_step m (b4_conjTuple a T) = b4_conjTuple a (b65s_step m T) := by
      obtain ⟨i, _, rfl | rfl⟩ := hw m List.mem_cons_self
      · funext k
        exact (b66h_braid_map (MulAut.conj a).toMonoidHom i T k).symm
      · funext k
        exact (b66h_negStep_map (MulAut.conj a).toMonoidHom i T k).symm
    rw [hs, ih (fun m' hm' ↦ hw m' (List.mem_cons_of_mem _ hm'))]
    rfl

theorem b65v_path_change {X : Type*} [TopologicalSpace X] {x y : X}
    (β : Path x y) (η : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath β (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk η)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (β.symm.trans (η.trans β))) := by
  rfl

theorem b65v_generator_values_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (y : b6t_punctured c) (u₀ : D.atlas.π ⁻¹' {y})
    (ℓ : Fin 13 → FundamentalGroup (b6t_punctured c) y)
    (hmono : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (ℓ i) =
      MulOpposite.op (b65b_initial i)⁻¹)
    (Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured c) (β : Path (Ψ b63gP_basePoint) y)
    (hword : ∀ ρ : (FundamentalGroup (b6t_punctured c) y)ᵐᵒᵖ →* b4b_Group,
      b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
            (MulOpposite.unop (b66h_loop k)))))) =
      b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op (ℓ j)))⁻¹)) :
    ∃ w₁ : D.atlas.π ⁻¹' {Ψ b63gP_basePoint}, ∃ a : b4b_Group, ∀ k,
      MulOpposite.unop ((D.atlas.hπ.fundamentalGroupToMulOpposite w₁)
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint (b63gP_loops k))) =
      a * b4b_root k * a⁻¹ := by
  let φ := D.atlas.hπ.fundamentalGroupToMulOpposite u₀
  let ν : (FundamentalGroup (b6t_punctured c) y)ᵐᵒᵖ →* b4b_Group :=
    { toFun := fun η ↦ MulOpposite.unop (φ (MulOpposite.unop η))
      map_one' := by simp
      map_mul' := by intro η θ; simp }
  let T : Fin 13 → b4b_Group := fun k ↦ ν (MulOpposite.op
    (FundamentalGroup.fundamentalGroupMulEquivOfPath β
      (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
        (MulOpposite.unop (b66h_loop k)))))
  have hF : b65s_word b65b_word T = b65b_final := by
    rw [hword ν]
    have hν : (fun j ↦ (ν (MulOpposite.op (ℓ j)))⁻¹) = b65b_initial := by
      funext j
      simp only [ν, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, φ,
        hmono j, MulOpposite.unop_inv, inv_inv]
    rw [hν, b65b_path_replay]
  have hT : T = b4_conjTuple (b4b_generators 1) b65s_columnRoot := by
    apply b65v_word_injective b65b_word b66h_word_letters
    rw [hF, b65v_word_conj b65b_word b66h_word_letters, b65b_replay.1]
    funext k
    simp [b4_conjTuple, mul_assoc]
  obtain ⟨w₁, hw₁⟩ := b65u_basepoint_adjust D.atlas.π D.atlas.hπ β.symm u₀
  have hadj : ∀ η : FundamentalGroup (b6t_punctured c) (Ψ b63gP_basePoint),
      D.atlas.hπ.fundamentalGroupToMulOpposite w₁ η =
        φ (FundamentalGroup.fundamentalGroupMulEquivOfPath β η) := by
    intro η
    have hback : ∀ θ : FundamentalGroup (b6t_punctured c) y,
        D.atlas.hπ.fundamentalGroupToMulOpposite w₁
          (FundamentalGroup.fundamentalGroupMulEquivOfPath β.symm θ) = φ θ := by
      intro θ
      change D.atlas.hπ.fundamentalGroupToMulOpposite w₁
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β.symm
          (FundamentalGroup.fromPath θ.toPath)) = φ (FundamentalGroup.fromPath θ.toPath)
      induction θ.toPath using Path.Homotopic.Quotient.ind with
      | mk θ => exact (b65v_path_change β.symm θ ▸ hw₁ θ)
    rw [← hback (FundamentalGroup.fundamentalGroupMulEquivOfPath β η)]
    congr 1
    change FundamentalGroup.fromPath η.toPath =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β.symm
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β (FundamentalGroup.fromPath η.toPath))
    induction η.toPath using Path.Homotopic.Quotient.ind with
    | mk η =>
      have h₁ := b65v_path_change β η
      have h₂ := b65v_path_change β.symm (β.symm.trans (η.trans β))
      calc
        _ = FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              (β.symm.symm.trans ((β.symm.trans (η.trans β)).trans β.symm))) := by
          congr 1
          simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
            Path.symm_symm]
          simp only [← Path.Homotopic.Quotient.trans_assoc,
            Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.symm_trans,
            Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]
          simp only [Path.Homotopic.Quotient.trans_assoc,
            Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]
        _ = _ := h₂.symm
        _ = _ := congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath β.symm) h₁.symm
  refine ⟨w₁, b4b_generators 1, fun k ↦ ?_⟩
  have ht := congrFun hT k.rev
  change MulOpposite.unop (φ (FundamentalGroup.fundamentalGroupMulEquivOfPath β
    (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
      ((b63gP_loops k.rev.rev)⁻¹)))) = _ at ht
  rw [Fin.rev_rev, map_inv, map_inv, map_inv, MulOpposite.unop_inv] at ht
  rw [hadj]
  have hv := congrArg Inv.inv ht
  simpa only [inv_inv, b4_conjTuple, b65s_columnRoot, Fin.rev_rev, mul_inv_rev, mul_assoc] using hv


end HodgeLean.Foundations.Program
