import HodgeLean.Foundations.Program.NumeratorJetRecurrence

/-! # Scalar denominator series in the Schlesinger field -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- A linear denominator has its geometric Taylor series, including a zero numerator. -/
theorem b65e_affineRatio_series (d w : ℂ) (hd : d ≠ 0) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ w / (d + θ * w)) P 0 ∧
      ∀ n : ℕ, P.coeff n = (w / d) * (-w / d) ^ n := by
  let L : ℂ →L[ℂ] ℂ := (-w / d) • ContinuousLinearMap.id ℂ ℂ
  have hh : HasFPowerSeriesAt (fun z : ℂ ↦ (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (L 0) := by
    simpa only [map_zero] using (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have hc := hh.compContinuousLinearMap (u := L) (x := 0)
  have hs := hc.const_smul (c := w / d)
  refine ⟨(w / d) • (formalMultilinearSeries_geometric ℂ ℂ).compContinuousLinearMap L, ?_, ?_⟩
  · convert hs using 1
    funext θ
    have he : d + θ * w = d * (1 - L θ) := by
      simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      field_simp
      ring
    rw [he, div_eq_mul_inv, mul_inv]
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  · intro n
    change (w / d) * (formalMultilinearSeries_geometric ℂ ℂ) n (L ∘ fun _ ↦ 1) = _
    simp [formalMultilinearSeries_geometric, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      L, List.prod_ofFn, Finset.prod_const, div_pow]

/-- The pole functions are affine with the stated velocities. -/
theorem b65e_poles_affine (p : Fin 12 → ℂ) (θ : ℂ) (q : Fin 4 ⊕ Fin 12) :
    b65p_poles p θ q = b65p_poles p 0 q + θ * b65p_velocity p q := by
  cases q <;> simp [b65p_poles, b65p_velocity]

/-- Every off-diagonal pole-ratio factor has the explicit geometric coefficients. -/
theorem b65e_poleRatio_series (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q r : Fin 4 ⊕ Fin 12) (hqr : q ≠ r) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦
        (b65p_velocity p q - b65p_velocity p r) /
          (b65p_poles p θ q - b65p_poles p θ r)) P 0 ∧
      ∀ n : ℕ, P.coeff n =
        ((b65p_velocity p q - b65p_velocity p r) /
          (b65p_poles p 0 q - b65p_poles p 0 r)) *
        (-(b65p_velocity p q - b65p_velocity p r) /
          (b65p_poles p 0 q - b65p_poles p 0 r)) ^ n := by
  have hd : b65p_poles p 0 q - b65p_poles p 0 r ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hqr (O.poles_injective 0 (Metric.mem_ball_self O.radius_pos) h)
  obtain ⟨P, hP, hc⟩ := b65e_affineRatio_series _
    (b65p_velocity p q - b65p_velocity p r) hd
  refine ⟨P, ?_, hc⟩
  convert hP using 1
  funext θ
  rw [b65e_poles_affine p θ q, b65e_poles_affine p θ r]
  congr 1
  ring

end HodgeLean.Foundations.Program
