import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMarking
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathWord
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathCorrection

/-! # Word transport retaining the certified ambient motion -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The inverse word endpoint followed by certified transport has the required loop-word action.
This statement retains the two punctured-sphere factors and their literal composite.
Source: `b65b_path_lasso_transport`; `b65v_word_endpoint`; B65-BRAIDCERT REPORT §1.5. -/
theorem rtc_marked_word_stage (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) :
    ∃ E : OnePoint ℂ ≃ₜ OnePoint ℂ,
    ∃ F : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ F (t, z))) ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, F (t, OnePoint.infty) = OnePoint.infty) ∧
      (∀ t j, F (t, (b65x_ext p 0 j : OnePoint ℂ)) =
        (b65x_ext p t j : OnePoint ℂ)) ∧
      (∀ z, F (1, z) = E z) ∧
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
      (∀ z, (h z : OnePoint ℂ) = E (b65x_mob z)) ∧
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 12, H 1 (mr_marks k : OnePoint ℂ) =
        b6_branch mr_base (b65u_endpointPerm k.castSucc)) ∧
    ∃ w : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
      (∀ z, (w z : OnePoint ℂ) = H 1 z) ∧
    ∃ C : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ C (t, z))) ∧
      (∀ z, C (0, z) = z) ∧
      (∀ t, C (t, OnePoint.infty) = OnePoint.infty) ∧
    ∃ Φ : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z, C (1, z) = Φ z) ∧
    ∃ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, Ψ z = e (h.symm (w.symm z))) ∧
      (∀ z, (Ψ z : OnePoint ℂ) = Φ z) ∧
      (∀ z, Φ z = b65p_mobius (p 10) (p 11)
        ((b65x_mob.trans E).symm ((H 1).symm z))) ∧
      ∃ hb : Ψ b63gP_basePoint = e (b65s_inclusion x),
        ∀ ρ : (FundamentalGroup (b6t_punctured (b65z_centre p))
            (e (b65s_inclusion x)))ᵐᵒᵖ →* b4b_Group,
          b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
            (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
              (MulOpposite.unop (b66h_loop k))))) =
          b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op
            (FundamentalGroup.map ((⟨e, e.continuous⟩ :
              C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
              (FundamentalGroup.fromPath ⟦δ j⟧))))⁻¹) := by
  obtain ⟨E, F, hFb, hF0, hFI, hFQ, hFe, _, h, hh, γ, _, _, _, htrace, _, hmove⟩ :=
    rtc_path_lasso_motion x δ hδ p hp
  obtain ⟨H, hH, hH0, hHI, hHB, hHm, w, hwH, hw, hact⟩ :=
    b65v_word_endpoint b65b_word b66h_word_letters
  have hbase : h (b65s_inclusion x) = b63gP_basePoint := by
    apply Subtype.ext
    change (h (b65s_inclusion x) : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)
    have hh := htrace 0 0
    simpa [mr_curve_zero] using hh
  have hbase' : h.symm b63gP_basePoint = b65s_inclusion x :=
    h.symm_apply_eq.mpr hbase.symm
  have hw' : w.symm b63gP_basePoint = b63gP_basePoint :=
    w.symm_apply_eq.mpr hw.symm
  let Θ := h.symm.trans e
  have hΘ : Θ b63gP_basePoint = e (b65s_inclusion x) := congrArg e hbase'
  let Ψ := w.symm.trans Θ
  have hb : Ψ b63gP_basePoint = e (b65s_inclusion x) := by
    change Θ (w.symm b63gP_basePoint) = _
    rw [hw', hΘ]
  have ha := b65x_witness_ne_zero p hp 10
  have hb' := b65x_witness_ne_zero p hp 11
  have hab : p 11 - p 10 ≠ 0 := sub_ne_zero.mpr (fun hh ↦ by
    have hi := b65x_witness_injective p hp hh
    norm_num at hi)
  let L := b65p_mobiusHomeomorph (p 10) (p 11) ha hb' hab
  have hL (z : OnePoint ℂ) : L z = b65p_mobius (p 10) (p 11) z :=
    congrFun (b65p_mobiusHomeomorph_apply _ _ ha hb' hab) z
  let Φ := (H 1).symm.trans ((b65x_mob.trans E).symm.trans L)
  have hhs (z : b6t_punctured mr_base) :
      (h.symm z : OnePoint ℂ) = (b65x_mob.trans E).symm z := by
    apply (b65x_mob.trans E).injective
    rw [Homeomorph.apply_symm_apply]
    exact (hh (h.symm z)).symm.trans (congrArg Subtype.val (h.apply_symm_apply z))
  have hws (z : b6t_punctured mr_base) :
      (w.symm z : OnePoint ℂ) = (H 1).symm z := by
    apply (H 1).injective
    rw [Homeomorph.apply_symm_apply]
    exact (hwH (w.symm z)).symm.trans (congrArg Subtype.val (w.apply_symm_apply z))
  obtain ⟨D, hD, hD0, hD1, hDI⟩ := rtc_mobius_correction_isotopy _ _ ha hb' hab
  let G : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ H q.1 q.2, hH⟩
  have hG0 (z) : G (0, z) = z := by change H 0 z = z; rw [hH0]; rfl
  obtain ⟨C, hC, hC0, hCI, hC1⟩ := rtc_composite_motion F G D hFb
    (fun t ↦ (H t).bijective) hD hF0 hG0 hD0 hFI hHI hDI E (H 1) hFe (fun _ ↦ rfl)
  have hCΦ (z) : C (1, z) = Φ z := by
    rw [hC1, hD1]
    exact (hL _).symm
  refine ⟨E, F, hFb, hF0, hFI, hFQ, hFe, h, hh, H, hH, hH0, hHI, hHB, ?_, w, hwH, C, hC, hC0, hCI, Φ, hCΦ, Ψ, fun _ ↦ rfl, ?_, ?_, hb, ?_⟩
  · simpa only [b65v_endpoint_word.1] using hHm
  · intro z
    change (e (h.symm (w.symm z)) : OnePoint ℂ) = _
    rw [he, hhs, hws]
    exact (hL _).symm
  · intro z
    exact hL _
  intro ρ
  let ν := ρ.comp (MonoidHom.op (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb))
  have hcancel (η : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint) :
      FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
        (FundamentalGroup.mapOfEq ⟨w, w.continuous⟩ hw η) =
      FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ η := by
    symm
    apply rtc_mapOfEq_comp _ _ _ hw hb hΘ _ η
    intro z
    change Θ z = Θ (w.symm (w z))
    rw [w.symm_apply_apply]
  have hword : b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
        (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
          (MulOpposite.unop (b66h_loop k))))) =
      fun k ↦ ρ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ
        (MulOpposite.unop (b66h_loop k)))) := by
    funext k
    exact (hact ν k).symm.trans (congrArg (fun η ↦ ρ (MulOpposite.op η))
      (hcancel (MulOpposite.unop (b66h_loop k))))
  rw [hword]
  let f : C(b65s_sphere, b6t_punctured (b65z_centre p)) := ⟨e, e.continuous⟩
  let μ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group :=
    { toFun := fun η ↦ ρ (MulOpposite.op ((FundamentalGroup.map f _ η)⁻¹))
      map_one' := by simp
      map_mul' := by intros; simp [mul_inv_rev] }
  have hloops (i : Fin 13) :
      FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ (b63gP_loops i) =
        FundamentalGroup.map f _
          (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦γ i⟧)) := by
    let M : Path b63gP_basePoint b63gP_basePoint :=
      (((γ i).map b65s_inclusion.continuous).map h.continuous).cast hbase.symm hbase.symm
    have hM : FundamentalGroup.fromPath ⟦M⟧ = b63gP_loops i :=
      b65x_loops_eq i M (htrace i)
    rw [← hM]
    change FundamentalGroup.mapOfEq _ hΘ
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk M)) = _
    rw [b66h_mapOfEq_fromPath]
    change FundamentalGroup.fromPath ⟦(M.map Θ.continuous).cast hΘ.symm hΘ.symm⟧ =
      FundamentalGroup.fromPath ⟦((γ i).map b65s_inclusion.continuous).map f.continuous⟧
    congr 1
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change e (h.symm (h (b65s_inclusion (γ i t)))) = _
    rw [h.symm_apply_apply]
    rfl
  have hright := funext (hmove μ)
  simp only [b66h_loop, MulOpposite.unop_op, map_inv, hloops]
  simpa only [μ, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.op_inv, map_inv,
    rtc_map_comp, f, b65b_pathWord] using hright


end HodgeLean.Foundations.Program
