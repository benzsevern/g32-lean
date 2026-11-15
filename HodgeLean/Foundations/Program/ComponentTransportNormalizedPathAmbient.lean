import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAffine
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathTracks

/-! # Normalizing an ambient realization with ordered finite tracks -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Moving affine normalization carries an ambient realization to the normalized chart.
Source: `rtc_certificate_normalized_tracks`; `rtc_affine_family_continuous`. -/
theorem rtc_normalized_ambient_family (p : Fin 12 → ℂ)
    (P : C(unitInterval, Fin 12 → ℂ)) (hinj : ∀ t, Function.Injective (P t))
    (hstart : ∀ k : Fin 12, P 0 k = (Fin.append mr_base ![0, 1] : Fin 12 → ℂ) k)
    (hend : ∀ k : Fin 12, P 1 k =
      (Fin.append (b65z_centre p) ![0, 1, 0] : Fin 13 → ℂ)
        (b65u_endpointPerm.symm k.castSucc))
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hH0 : ∀ z, H (0, z) = z)
    (hHI : ∀ t, H (t, OnePoint.infty) = OnePoint.infty)
    (hHP : ∀ t k, H (t, (mr_marks k : OnePoint ℂ)) = (P t k : OnePoint ℂ)) :
    ∃ γ : C(unitInterval, Fin 10 → ℂ),
      (∀ t, γ t ∈ b6_chart) ∧ γ 0 = mr_base ∧ γ 1 = b65v_relabelCentre p ∧
    ∃ F : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ F (t, z))) ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t j, F (t, b6_branch mr_base j) = b6_branch (γ t) j) ∧
      (∀ t z, F (t, z) = OnePoint.map
        (fun w ↦ (w - P t 10) / (P t 11 - P t 10)) (H (t, z))) := by
  obtain ⟨γ, hγ, hchart, hγ0, hγ1⟩ :=
    rtc_certificate_normalized_tracks p P hinj hstart hend
  have hd (t : unitInterval) : P t 11 - P t 10 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := hinj t h
    norm_num at hh
  let A : C(unitInterval, ℂ) :=
    ⟨fun t ↦ (P t 11 - P t 10)⁻¹,
      (((continuous_apply 11).comp P.continuous).sub
        ((continuous_apply 10).comp P.continuous)).inv₀ hd⟩
  let B : C(unitInterval, ℂ) :=
    ⟨fun t ↦ -P t 10 / (P t 11 - P t 10),
      ((continuous_apply 10).comp P.continuous).neg.div
        (((continuous_apply 11).comp P.continuous).sub
          ((continuous_apply 10).comp P.continuous)) hd⟩
  have hc : Continuous (fun q : unitInterval × OnePoint ℂ ↦
      OnePoint.map (fun w ↦ (w - P q.1 10) / (P q.1 11 - P q.1 10)) q.2) := by
    have heq (t : unitInterval) :
        (fun w ↦ (w - P t 10) / (P t 11 - P t 10)) = (fun w ↦ A t * w + B t) := by
      funext w
      simp only [A, B, ContinuousMap.coe_mk, div_eq_mul_inv]
      ring
    simp_rw [heq]
    exact rtc_affine_family_continuous A B (fun t ↦ inv_ne_zero (hd t))
  let F : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ OnePoint.map (fun w ↦ (w - P q.1 10) / (P q.1 11 - P q.1 10)) (H q),
      hc.comp (continuous_fst.prodMk H.continuous)⟩
  have hF (t : unitInterval) (z : OnePoint ℂ) : F (t, z) =
      OnePoint.map (fun w ↦ (w - P t 10) / (P t 11 - P t 10)) (H (t, z)) := rfl
  refine ⟨γ, hchart, hγ0, hγ1, F, ?_, ?_, ?_, hF⟩
  · intro t
    change Function.Bijective ((OnePoint.map
      (fun w ↦ (w - P t 10) / (P t 11 - P t 10))) ∘ (fun z ↦ H (t, z)))
    apply Function.Bijective.comp _ (hH t)
    apply b65x_map_bijective
    constructor
    · intro z w he
      exact sub_left_injective ((div_left_inj' (hd t)).mp he)
    · intro z
      refine ⟨z * (P t 11 - P t 10) + P t 10, ?_⟩
      dsimp only
      rw [add_sub_cancel_right, mul_div_cancel_right₀ _ (hd t)]
  · intro z
    rw [hF, hH0]
    have h0 : P 0 10 = 0 := (hstart 10).trans (Fin.append_right _ _ (0 : Fin 2))
    have h1 : P 0 11 = 1 := (hstart 11).trans (Fin.append_right _ _ (1 : Fin 2))
    rw [h0, h1]
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z => simp only [OnePoint.map_some, sub_zero, div_one]
  · intro t j
    have hfinite (k : Fin 12) : F (t, b6_branch mr_base k.castSucc) =
        (((P t k - P t 10) / (P t 11 - P t 10) : ℂ) : OnePoint ℂ) := by
      rw [hF, b65x_branch_cast, hHP, OnePoint.map_some]
    by_cases hj : j.val < 10
    · let k : Fin 10 := ⟨j.val, hj⟩
      have he : j = (k.castAdd 2).castSucc := by apply Fin.ext; rfl
      rw [he, hfinite, ← hγ]
      change (γ t k : OnePoint ℂ) = b6_branch (γ t) (k.castAdd 3)
      unfold b6_branch
      exact (Fin.append_left (fun i ↦ (γ t i : OnePoint ℂ)) _ k).symm
    · have hj' : j = 10 ∨ j = 11 ∨ j = 12 := by
        have := j.isLt
        rcases (show j.val = 10 ∨ j.val = 11 ∨ j.val = 12 by omega) with h | h | h
        · left; apply Fin.ext; exact h
        · right; left; apply Fin.ext; exact h
        · right; right; apply Fin.ext; exact h
      rcases hj' with rfl | rfl | rfl
      · change F (t, b6_branch mr_base (10 : Fin 12).castSucc) = ((0 : ℂ) : OnePoint ℂ)
        simpa only [sub_self, zero_div] using hfinite 10
      · change F (t, b6_branch mr_base (11 : Fin 12).castSucc) = ((1 : ℂ) : OnePoint ℂ)
        simpa only [div_self (hd t)] using hfinite 11
      · change F (t, OnePoint.infty) = OnePoint.infty
        rw [hF, hHI]
        rfl

/-- The final moving normalization is inverse to the specified affine endpoint.
Source: the endpoint formula in spec-chs, geometric composite, item 3. -/
theorem rtc_affine_normalization_cancel (a : ℂ) (ha : a ≠ 0)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMz : ∀ z : ℂ, M z = ((a * (1 - z) : ℂ) : OnePoint ℂ))
    (hMI : M OnePoint.infty = OnePoint.infty) (z : OnePoint ℂ) :
    M (OnePoint.map (fun w ↦ (w - a) / (0 - a)) z) = z := by
  induction z using OnePoint.rec with
  | infty => exact hMI
  | coe z =>
    rw [OnePoint.map_some, hMz]
    congr 1
    field_simp [ha]
    <;> ring

end HodgeLean.Foundations.Program
