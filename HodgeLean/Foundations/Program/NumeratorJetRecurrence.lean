import HodgeLean.Foundations.Program.KernelFramesFamilyAnalytic

/-! # Scalar coefficient recurrences for the stage 5e path -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Differentiation shifts scalar Taylor coefficients and multiplies by the order. -/
theorem b65e_derivative_coeff {f g : ℂ → ℂ}
    {P Q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (hQ : HasFPowerSeriesAt g Q 0)
    (hg : g =ᶠ[𝓝 0] deriv f) (n : ℕ) :
    Q.coeff n = (n + 1 : ℂ) * P.coeff (n + 1) := by
  obtain ⟨r, hr⟩ := hP
  let L : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hd := L.comp_hasFPowerSeriesOnBall hr.fderiv
  have he : (L ∘ fderiv ℂ f) = deriv f := by
    funext z
    rfl
  rw [he] at hd
  have hPQ := hQ.eq_formalMultilinearSeries_of_eventually hd.hasFPowerSeriesAt hg
  rw [hPQ]
  change P.derivSeries.coeff n 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul]
  norm_cast

/-- The Schlesinger equation evaluated at a matrix entry. -/
theorem b65e_residue_hasDerivAt (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) {θ : ℂ}
    (hθ : θ ∈ ball (0 : ℂ) O.radius) :
    HasDerivAt (fun θ ↦ b65q_res O.residue θ q i j)
      (∑ r : Fin 4 ⊕ Fin 12, if r = q then 0 else
        ((b65p_velocity p q - b65p_velocity p r) /
          (b65p_poles p θ q - b65p_poles p θ r)) *
        (b65q_res O.residue θ r * b65q_res O.residue θ q -
          b65q_res O.residue θ q * b65q_res O.residue θ r) i j) θ := by
  have h := (b65q_entryCLM i j).hasFDerivAt.comp_hasDerivAt θ (O.schlesinger θ hθ q)
  have hm : b65q_mat
      (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ)
        (O.residue θ) q) =
      ∑ r : Fin 4 ⊕ Fin 12, if r = q then 0 else
        ((b65p_velocity p q - b65p_velocity p r) /
          (b65p_poles p θ q - b65p_poles p θ r)) •
        (b65q_res O.residue θ r * b65q_res O.residue θ q -
          b65q_res O.residue θ q * b65q_res O.residue θ r) := by
    change b65q_matAlg _ = _
    simp only [b65p_schlesingerField, map_sum, apply_ite, map_zero, map_smul,
      map_sub, map_mul, b65q_matAlg_apply, b65q_res]
  simp only [Function.comp_def, b65q_entryCLM_apply] at h
  rw [hm] at h
  simp only [Matrix.sum_apply] at h
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> rfl

/-- The scalar right-hand side in matrix coordinates. -/
def b65e_fieldEntry (p : Fin 12 → ℂ)
    (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) : ℂ :=
  ∑ r : Fin 4 ⊕ Fin 12, if r = q then 0 else
    ((b65p_velocity p q - b65p_velocity p r) /
      (b65p_poles p θ q - b65p_poles p θ r)) *
    (b65q_res R θ r * b65q_res R θ q - b65q_res R θ q * b65q_res R θ r) i j

/-- The analytic residue series and field series satisfy the differential recurrence at every order. -/
theorem b65e_residue_series_recurrence (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) :
    ∃ P Q : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
      HasFPowerSeriesAt (fun θ ↦ b65e_fieldEntry p O.residue θ q i j) Q 0 ∧
      ∀ n : ℕ, Q.coeff n = (n + 1 : ℂ) * P.coeff (n + 1) := by
  obtain ⟨P, hP⟩ := b65q_MatAn.res O q i j 0 (Metric.mem_ball_self O.radius_pos)
  obtain ⟨Q, hQ⟩ := hP.analyticAt.deriv
  have he : (fun θ ↦ b65e_fieldEntry p O.residue θ q i j) =ᶠ[𝓝 0]
      deriv (fun θ ↦ b65q_res O.residue θ q i j) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) O.radius_pos] with θ hθ
    exact (b65e_residue_hasDerivAt p O q i j hθ).deriv.symm
  have hQ' := hQ.congr he.symm
  exact ⟨P, Q, hP, hQ', b65e_derivative_coeff hP hQ' he⟩

/-- The first coefficient is the field at the initial residues; it does not depend on a series choice. -/
theorem b65e_residue_coeff_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4)
    {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0) :
    P.coeff 1 = b65e_fieldEntry p (fun _ ↦ b65p_initialResidue) 0 q i j := by
  have h := hP.hasDerivAt.unique
    (b65e_residue_hasDerivAt p O q i j (Metric.mem_ball_self O.radius_pos))
  change P.coeff 1 = b65e_fieldEntry p O.residue 0 q i j at h
  simpa only [b65e_fieldEntry, b65q_res, O.residue_zero] using h

end HodgeLean.Foundations.Program
