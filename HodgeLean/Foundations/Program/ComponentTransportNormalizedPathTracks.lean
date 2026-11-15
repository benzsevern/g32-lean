import HodgeLean.Foundations.Program.ComponentTransportNormalized
import HodgeLean.Foundations.Program.RadialTransportComparison

/-! # Endpoints of the moving affine normalization -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Certificate tracks with the inverse endpoint permutation normalize to the relabelled centre.
Source: `rtc_normalized_tracks`; `b65v_endpoint_word`; the geometric composite in spec-chs. -/
theorem rtc_certificate_normalized_tracks (p : Fin 12 → ℂ)
    (P : C(unitInterval, Fin 12 → ℂ)) (hinj : ∀ t, Function.Injective (P t))
    (hstart : ∀ k : Fin 12, P 0 k = (Fin.append mr_base ![0, 1] : Fin 12 → ℂ) k)
    (hend : ∀ k : Fin 12, P 1 k =
      (Fin.append (b65z_centre p) ![0, 1, 0] : Fin 13 → ℂ)
        (b65u_endpointPerm.symm k.castSucc)) :
    ∃ γ : C(unitInterval, Fin 10 → ℂ),
      (∀ t k, γ t k = (P t (k.castAdd 2) - P t 10) / (P t 11 - P t 10)) ∧
      (∀ t, γ t ∈ b6_chart) ∧ γ 0 = mr_base ∧ γ 1 = b65v_relabelCentre p := by
  have h110 : P 1 10 = b65z_centre p 8 := by
    rw [hend, show (10 : Fin 12).castSucc = (10 : Fin 13) from rfl,
      b65v_endpoint_word.2.1]
    exact Fin.append_left _ _ (8 : Fin 10)
  have h111 : P 1 11 = 0 := by
    rw [hend, show (11 : Fin 12).castSucc = (11 : Fin 13) from rfl,
      b65v_endpoint_word.2.2.1]
    exact Fin.append_right _ _ (0 : Fin 3)
  have h8 : b65z_centre p 8 ≠ 0 := by
    intro hz
    have hh : P 1 10 = P 1 11 := h110.trans (hz.trans h111.symm)
    have he := hinj 1 hh
    norm_num at he
  have hendpoint (k : Fin 10) :
      (P 1 (k.castAdd 2) - P 1 10) / (P 1 11 - P 1 10) = b65v_relabelCentre p k := by
    rw [h110, h111, hend]
    change (_ - b65z_centre p 8) / (0 - b65z_centre p 8) =
      1 - _ / b65z_centre p 8
    have hk : (k.castAdd 2).castSucc = k.castAdd 3 := by apply Fin.ext; rfl
    rw [hk]
    field_simp
    <;> ring
  obtain ⟨γ, hformula, hchart, hγ1⟩ := rtc_normalized_tracks P hinj _ hendpoint
  refine ⟨γ, hformula, hchart, ?_, hγ1⟩
  funext k
  rw [hformula, hstart, hstart, hstart]
  have h0 : (Fin.append mr_base ![0, 1] : Fin 12 → ℂ) 10 = 0 :=
    Fin.append_right _ _ (0 : Fin 2)
  have h1 : (Fin.append mr_base ![0, 1] : Fin 12 → ℂ) 11 = 1 :=
    Fin.append_right _ _ (1 : Fin 2)
  rw [h0, h1, Fin.append_left]
  simp

end HodgeLean.Foundations.Program
