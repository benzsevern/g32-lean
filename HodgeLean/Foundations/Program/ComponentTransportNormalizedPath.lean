import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathReparametrization
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathTracks
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathWord
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMarkedWord
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAmbient
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAffineIsotopy
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathComposite

import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathEndpoints
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathBasepoint

/-! # Normalized path restoration infrastructure
The path-class, universal subdivision, endpoint-coordinate and punctured-word stages.
The ambient realization and moving affine normalization have supporting interfaces.
Ordered endpoint specialization and common base-point transport give
the frozen signature of `b65v_normalized_path`.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- A chosen ambient chart motion has a path-class representative for which every valid
radial subdivision has the same based-loop action along one base-point track.
Source: `b65v_controlled_path`; `rtc_finite_comparison`; `rtc_configuration_comparison`;
Birman, Braids, Links, and Mapping Class Groups, Chapter 1, §1.4. -/
theorem rtc_controlled_radial_transport {a b : b6_chart} (α : Path a b)
    (hb : ¬ ∀ i, dist (b.val i) (a.val i) ≤ b6t_radius a.val)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hH0 : ∀ z, H (0, z) = z)
    (hHm : ∀ t j, H (t, b6_branch a.val j) = b6_branch (α t).val j)
    (A : b6t_punctured a.val ≃ₜ b6t_punctured b.val)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z)) (x : b6t_punctured a.val) :
    ∃ γ : Path a b, α.Homotopic γ ∧
      ∀ N : ℕ, 0 < N →
        (∀ k < N, b65y_sample
          ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩ N (k + 1) ∈
            b6t_polydisc (b65y_sample
              ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩ N k)) →
        ∀ R : b6t_punctured a.val ≃ₜ b6t_punctured b.val,
          (∀ z, (R z : OnePoint ℂ) = b65y_radial (b65y_sample
            ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩ N) N z) →
          ∃ β : Path (R x) (A x), ∀ η : FundamentalGroup (b6t_punctured a.val) x,
            FundamentalGroup.fundamentalGroupMulEquivOfPath β
              (FundamentalGroup.map ⟨R, R.continuous⟩ x η) =
                FundamentalGroup.map ⟨A, A.continuous⟩ x η := by
  obtain ⟨γ, hαγ, hregions⟩ := b65v_controlled_path α hb
  let g : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩
  let Q : C(unitInterval × unitInterval, b6_chart) :=
    ⟨fun t ↦ γ t.2, γ.continuous.comp continuous_snd⟩
  obtain ⟨F, hFb, hF0, hFm⟩ := rtc_chart_square Q
  let G : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ F ((0, q.1), q.2), F.continuous.comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)⟩
  have hGb : ∀ t, Function.Bijective (fun z ↦ G (t, z)) := hFb 0
  have hG0 : ∀ z, G (0, z) = z := hF0 0
  have hGm : ∀ t j, G (t, b6_branch a.val j) = b6_branch (γ t).val j := by
    intro t j
    have hh := hFm 0 t j
    change G (t, b6_branch (γ 0).val j) = b6_branch (γ t).val j at hh
    simpa only [Path.source] using hh
  obtain ⟨L, hLb, hL0, hL1, hLm⟩ := rtc_configuration_comparison γ α hαγ.symm
    G H hGb hH hG0 hH0 hGm hHm
  refine ⟨γ, hαγ, fun N hN hsteps R hR ↦ ?_⟩
  have hgm : ∀ t j, G (t, b6_branch (g 0) j) = b6_branch (g t) j := by
    simpa only [g, ContinuousMap.coe_mk, Path.source] using hGm
  obtain ⟨K, hKb, hK0, hK1, hKm⟩ := rtc_finite_comparison g
    (fun t ↦ (γ t).property) G hGb hG0 hgm N hN hsteps (hregions N hN hsteps)
  let f₀ : C(OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun z ↦ K (0, z), K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let f₁ : C(OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun z ↦ G (1, z), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let f₂ : C(OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun z ↦ H (1, z), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hKm' : ∀ t j, K (t, b6_branch a.val j) = b6_branch b.val j := by
    simpa only [g, ContinuousMap.coe_mk, Path.source, Path.target] using hKm
  let D := (rtc_fixed_homotopy f₀ f₁ (b6_branch a.val) (b6_branch b.val)
    K hKb (fun _ ↦ rfl) hK1 hKm').trans
      (rtc_fixed_homotopy f₁ f₂ (b6_branch a.val) (b6_branch b.val) L hLb hL0 hL1 hLm)
  apply rtc_homotopy_action (rtc_restrict_comparison a.val b.val R A D.toContinuousMap
    (fun t ↦ (D.prop t).1) (fun z ↦ ?_) (fun z ↦ ?_) (fun t ↦ (D.prop t).2)) x
  · exact (D.map_zero_left z).trans ((hK0 z).trans (hR z).symm)
  · exact (D.map_one_left z).trans (hA z).symm

/-- Normalized certificate transport with one base-point path for every loop and representation.
Source: Birman, Braids, Links, and Mapping Class Groups, Chapter 1, §1.4;
Hatcher, Algebraic Topology, §1.1; B65-BRAIDCERT REPORT §1.5. -/
theorem b65v_normalized_path (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMz : ∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ))
    (hMinf : M OnePoint.infty = OnePoint.infty) :
    ∃ γ : C(unitInterval, Fin 10 → ℂ), (∀ τ, γ τ ∈ b6_chart) ∧ γ 0 = mr_base ∧
      γ 1 = b65v_relabelCentre p ∧
      ∀ N : ℕ, 0 < N →
        (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
        ∀ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
          (∀ z, (Ψ z : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N z)) →
          (∀ j, M (b65y_radial (b65y_sample γ N) N (b6_branch mr_base (b65u_endpointPerm j))) =
            b6_branch (b65z_centre p) j) ∧
          ∃ β : Path (Ψ b63gP_basePoint) (e (b65s_inclusion x)),
            ∀ ρ : (FundamentalGroup (b6t_punctured (b65z_centre p)) (e (b65s_inclusion x)))ᵐᵒᵖ →*
                b4b_Group,
              b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
                (FundamentalGroup.fundamentalGroupMulEquivOfPath β
                  (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
                    (MulOpposite.unop (b66h_loop k)))))) =
              b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op
                (FundamentalGroup.map ((⟨e, e.continuous⟩ :
                  C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
                  (FundamentalGroup.fromPath ⟦δ j⟧))))⁻¹) := by
  obtain ⟨E, F, hFb, hF0, hFI, hFQ, hFe, h, hh, H, hH, hH0, hHI, hHB,
    hHm, w, hwH, C, hCb, hC0, hCI, Φ, hCΦ, A₀, hA₀, hAΦ, hΦ, hb, hword⟩ :=
    rtc_marked_word_stage p hp e he x δ hδ
  have hne := b65x_witness_ne_zero p hp
  have hab : p 11 - p 10 ≠ 0 := sub_ne_zero.mpr (fun he ↦ by
    have hi := b65x_witness_injective p hp he
    norm_num at hi)
  have hE (j : Fin 12) : E (b65x_rnorm p j : OnePoint ℂ) = (mr_marks j : OnePoint ℂ) := by
    have hq := hFQ 1 (Fin.castAdd 4 j)
    rw [hFe] at hq
    have h0 : b65x_ext p 0 (Fin.castAdd 4 j) = b65x_rnorm p j := by
      rw [b65x_ext_cfg]; simp
    have h1 : b65x_ext p 1 (Fin.castAdd 4 j) = mr_marks j := by
      rw [b65x_ext_cfg, ite_eq_right (by norm_num)]
      rw [show (2 * 1 - 1 : ℝ) = 1 by norm_num, b65x_configuration_one]
    simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, h0, h1] using hq
  have hEI : E OnePoint.infty = OnePoint.infty := (hFe _).symm.trans (hFI 1)
  have hlabels := rtc_composite_endpoint_labels p hne hab E (H 1) Φ hE hEI hHm (hHI 1) hΦ
  obtain ⟨P, hPi, hP0, hP1, hPC⟩ := rtc_certificate_ambient_tracks p C hCb hC0 hCI
    (fun j ↦ (hCΦ _).trans (hlabels j))
  obtain ⟨g, hg, hg0, hg1, G, hGb, hG0, hGm, hG⟩ :=
    rtc_normalized_ambient_family p P hPi hP0 hP1 C hCb hC0 hCI hPC
  have hc : b65z_centre p ∈ b6_chart := ((b65p_normalized_path p hp).1.self_of_nhds).1
  obtain ⟨hc', hMl, hMd, hMid, hMc⟩ := b65v_relabel_normalization p hc M hMz hMinf
  let m := b65u_restrict M hMc
  let A := A₀.trans m.symm
  have hm (z : b6t_punctured (b65v_relabelCentre p)) : (m z : OnePoint ℂ) = M z := rfl
  have hmA (z : b6t_punctured mr_base) : m (A z) = A₀ z := m.apply_symm_apply _
  have h110 : P 1 10 = b65z_centre p 8 := by
    rw [hP1, show (10 : Fin 12).castSucc = (10 : Fin 13) from rfl,
      b65v_endpoint_word.2.1]
    exact Fin.append_left _ _ (8 : Fin 10)
  have h111 : P 1 11 = 0 := by
    rw [hP1, show (11 : Fin 12).castSucc = (11 : Fin 13) from rfl,
      b65v_endpoint_word.2.2.1]
    exact Fin.append_right _ _ (0 : Fin 3)
  have h8 : b65z_centre p 8 ≠ 0 := by
    intro hz
    have he := hPi 1 (h110.trans (hz.trans h111.symm))
    norm_num at he
  have hAG (z : b6t_punctured mr_base) : (A z : OnePoint ℂ) = G (1, z) := by
    apply M.injective
    rw [← hm, hmA, hAΦ, hG, h110, h111,
      rtc_affine_normalization_cancel _ h8 M hMz hMinf, hCΦ]
  let a : b6_chart := ⟨mr_base, mr_base_mem_chart⟩
  let b : b6_chart := ⟨b65v_relabelCentre p, hc'⟩
  let α : Path a b :=
    { toFun := fun t ↦ ⟨g t, hg t⟩
      continuous_toFun := g.continuous.subtype_mk _
      source' := Subtype.ext hg0
      target' := Subtype.ext hg1 }
  have hout : ¬ ∀ i, dist (b.val i) (a.val i) ≤ b6t_radius a.val := by
    intro hall
    exact (not_le.mpr (b65v_endpoint_outside p hp)) (hall 0)
  have hGm' : ∀ t j, G (t, b6_branch a.val j) = b6_branch (α t).val j := hGm
  obtain ⟨γ, hαγ, hrad⟩ := rtc_controlled_radial_transport α hout G hGb hG0 hGm' A hAG
    b63gP_basePoint
  let γc : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩
  have hγ0 : γc 0 = mr_base := congrArg Subtype.val γ.source
  have hγ1 : γc 1 = b65v_relabelCentre p := congrArg Subtype.val γ.target
  refine ⟨γc, fun t ↦ (γ t).property, hγ0, hγ1, fun N hN hsteps Ψ hΨ ↦ ?_⟩
  have hs0 : b65y_sample γc N 0 = mr_base := by
    simp only [b65y_sample, Nat.cast_zero, zero_div, Set.projIcc_left]
    exact hγ0
  have hs1 : b65y_sample γc N N = b65v_relabelCentre p := by
    simp only [b65y_sample, div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),
      Set.projIcc_right]
    exact hγ1
  refine ⟨b65v_radial_endpoint_labels p hc M hMz hMinf _ N hs0 hs1 hsteps, ?_⟩
  let R := Ψ.trans m.symm
  have hR (z : b6t_punctured mr_base) : (R z : OnePoint ℂ) =
      b65y_radial (b65y_sample γc N) N z := by
    apply M.injective
    change M (m.symm (Ψ z) : OnePoint ℂ) = _
    rw [← hm, m.apply_symm_apply, hΨ]
  obtain ⟨β, hβ⟩ := hrad N hN hsteps R hR
  obtain ⟨β', hβ'⟩ := rtc_postcompose_action ⟨R, R.continuous⟩ ⟨A, A.continuous⟩
    ⟨m, m.continuous⟩ ⟨Ψ, Ψ.continuous⟩ ⟨A₀, A₀.continuous⟩ b63gP_basePoint
    (fun z ↦ (m.apply_symm_apply (Ψ z)).symm) (fun z ↦ (hmA z).symm) hb β hβ
  refine ⟨β', fun ρ ↦ ?_⟩
  simp_rw [hβ']
  exact hword ρ


end HodgeLean.Foundations.Program
