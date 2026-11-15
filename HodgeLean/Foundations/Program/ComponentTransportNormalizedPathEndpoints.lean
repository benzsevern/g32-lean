import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathMarkedWord
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAmbient

/-! # Ordered endpoints of the ambient word motion -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- The retained certified motion and word permutation determine every endpoint label.
Source: `b65x_ext_cfg`; `b65p_mobius_labels`; `b65v_endpoint_word`. -/
theorem rtc_composite_endpoint_labels (p : Fin 12 → ℂ)
    (hne : ∀ j, p j ≠ 0) (hab : p 11 - p 10 ≠ 0)
    (E W Φ : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hE : ∀ j : Fin 12, E (b65x_rnorm p j : OnePoint ℂ) = (mr_marks j : OnePoint ℂ))
    (hEI : E OnePoint.infty = OnePoint.infty)
    (hW : ∀ j : Fin 12, W (mr_marks j : OnePoint ℂ) =
      b6_branch mr_base (b65u_endpointPerm j.castSucc))
    (hWI : W OnePoint.infty = OnePoint.infty)
    (hΦ : ∀ z, Φ z = b65p_mobius (p 10) (p 11)
      ((b65x_mob.trans E).symm (W.symm z))) :
    ∀ j, Φ (b6_branch mr_base (b65u_endpointPerm j)) =
      b6_branch (b65z_centre p) j := by
  have hfinite (j : Fin 12) :
      (b65x_mob.trans E) (p j : OnePoint ℂ) = (mr_marks j : OnePoint ℂ) := by
    change E (b65x_mob (p j : OnePoint ℂ)) = _
    rw [b65x_mob_coe (hne j)]
    exact hE j
  have hlabel (j : Fin 12) :
      b65p_mobius (p 10) (p 11) (p j : OnePoint ℂ) =
        b6_branch (b65z_centre p) j.castSucc := by
    have hh := b65p_mobius_labels p hne hab j.castSucc
    have hc : b65z_centre p = b65p_chartPoint p := by
      change b65p_chartPoint (b65p_moving p 0) = b65p_chartPoint p
      congr 1
      funext i
      simp [b65p_moving, b65p_poles]
    rw [hc]
    convert hh using 2
    fin_cases j <;> rfl
  intro j
  by_cases hj : j.val < 12
  · let k : Fin 12 := ⟨j.val, hj⟩
    have hjk : j = k.castSucc := by apply Fin.ext; rfl
    rw [hjk, hΦ, ← hW, W.symm_apply_apply,
      ← hfinite, Homeomorph.symm_apply_apply]
    exact hlabel k
  · have hj12 : j = 12 := by apply Fin.ext; have := j.isLt; omega
    subst j
    have hτ : b65u_endpointPerm (12 : Fin 13) = 12 := by decide +kernel
    rw [hτ]
    change Φ OnePoint.infty = OnePoint.infty
    rw [hΦ, show W.symm OnePoint.infty = OnePoint.infty from
      W.symm_apply_eq.mpr hWI.symm]
    have hz : (b65x_mob.trans E) ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
      change E (b65x_mob ((0 : ℂ) : OnePoint ℂ)) = _
      rw [b65x_mob_zero, hEI]
    rw [show (b65x_mob.trans E).symm OnePoint.infty = ((0 : ℂ) : OnePoint ℂ) from
      (b65x_mob.trans E).symm_apply_eq.mpr hz.symm]
    simp [b65p_mobius]

/-- A finite branch label agrees with the appended coordinate tuple.
Source: `b6_branch`; `Fin.append`. -/
theorem rtc_branch_finite (c : Fin 10 → ℂ) (j : Fin 13) (hj : j ≠ 12) :
    b6_branch c j =
      (((Fin.append c ![0, 1, 0] : Fin 13 → ℂ) j : ℂ) : OnePoint ℂ) := by
  fin_cases j <;> first | rfl | exact (hj rfl).elim

/-- Extract and reindex the finite tracks of a motion with the certificate endpoint labels.
Source: `rtc_finite_ambient_tracks`; `b65u_endpointPerm`. -/
theorem rtc_certificate_ambient_tracks (p : Fin 12 → ℂ)
    (C : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hC : ∀ t, Function.Bijective (fun z ↦ C (t, z)))
    (hC0 : ∀ z, C (0, z) = z)
    (hCI : ∀ t, C (t, OnePoint.infty) = OnePoint.infty)
    (hend : ∀ j, C (1, b6_branch mr_base (b65u_endpointPerm j)) =
      b6_branch (b65z_centre p) j) :
    ∃ P : C(unitInterval, Fin 12 → ℂ), (∀ t, Function.Injective (P t)) ∧
      (∀ k : Fin 12, P 0 k = (Fin.append mr_base ![0, 1] : Fin 12 → ℂ) k) ∧
      (∀ k : Fin 12, P 1 k =
        (Fin.append (b65z_centre p) ![0, 1, 0] : Fin 13 → ℂ)
          (b65u_endpointPerm.symm k.castSucc)) ∧
      ∀ t k, C (t, (mr_marks k : OnePoint ℂ)) = (P t k : OnePoint ℂ) := by
  have hinj : Function.Injective mr_marks := by
    intro i j he
    apply Fin.castSucc_injective
    apply mr_base_mem_chart
    apply_fun ((↑) : ℂ → OnePoint ℂ) at he
    simpa only [← b65x_branch_cast] using he
  obtain ⟨P, hP, hPC⟩ := rtc_finite_ambient_tracks mr_marks hinj C (fun t ↦ (hC t).1) hCI
  refine ⟨P, hP, ?_, ?_, fun t k ↦ (hPC t k).symm⟩
  · intro k
    apply OnePoint.coe_injective
    rw [hPC, hC0]
    fin_cases k <;> rfl
  · intro k
    apply OnePoint.coe_injective
    rw [hPC, ← b65x_branch_cast]
    have hj : b65u_endpointPerm.symm k.castSucc ≠ 12 := by
      intro he
      have hτ : b65u_endpointPerm (12 : Fin 13) = 12 := by decide +kernel
      have he' := congrArg b65u_endpointPerm he
      rw [Equiv.apply_symm_apply, hτ] at he'
      exact k.castSucc_ne_last he'
    have hh := hend (b65u_endpointPerm.symm k.castSucc)
    rw [Equiv.apply_symm_apply] at hh
    exact hh.trans (rtc_branch_finite _ _ hj)

end HodgeLean.Foundations.Program
