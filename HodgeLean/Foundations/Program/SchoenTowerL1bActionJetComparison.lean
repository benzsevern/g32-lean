import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeJets

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A first jet with zero residue on a regular parameter is determined by
its infinitesimal coefficient on that parameter. -/
theorem s2v_l1b_action_jet_linear_coefficient
    {R K : Type*} [CommRing R] [Field K] [Algebra K R]
    (φ : R →ₐ[K] PowerSeries K) (ψ : R →ₐ[K] DualNumber K)
    (u : R) (hu : φ u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp φ.toRingHom) = Ideal.span {u})
    (hzero : (ψ u).fst = 0) (r : R) :
    (ψ r).snd = PowerSeries.coeff 1 (φ r) * (ψ u).snd := by
  have hc (k : K) : φ (algebraMap K R k) = PowerSeries.C k := φ.commutes k
  have hd (k : K) : ψ (algebraMap K R k) = TrivSqZeroExt.inl k := ψ.commutes k
  have hdiv := s2v_l1b_rotation_parameter_division (algebraMap K R)
    (PowerSeries.constantCoeff.comp φ.toRingHom)
    (fun k => by change PowerSeries.constantCoeff (φ (algebraMap K R k)) = k
                 rw [hc, PowerSeries.constantCoeff_C]) u hker
  have hfst (w : R) : (ψ w).fst = PowerSeries.constantCoeff (φ w) := by
    obtain ⟨k, v, hv⟩ := hdiv w
    rw [hv]
    simp only [map_add, map_mul, hc, hd, hu, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_mul, hzero,
      PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, zero_mul, add_zero]
  obtain ⟨k, w, hw⟩ := hdiv r
  rw [hw]
  simp only [map_add, map_mul, hc, hd, hu, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, DualNumber.snd_mul, hzero, zero_mul, zero_add,
    PowerSeries.coeff_C_of_ne_zero (by omega : (1 : ℕ) ≠ 0),
    PowerSeries.coeff_one_mul, PowerSeries.coeff_one_X, PowerSeries.constantCoeff_X,
    mul_zero, add_zero, one_mul]
  rw [hfst, mul_comm]

end HodgeLean.Foundations.Program
