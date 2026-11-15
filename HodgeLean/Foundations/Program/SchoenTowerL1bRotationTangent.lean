import HodgeLean.Foundations.Program.SchoenTowerL1bRotationLinearization

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A scalar-preserving action on a principal residue kernel acts on the
first coefficient by the first coefficient of the image of its parameter. -/
theorem s2v_l1b_rotation_tangent_scalar
    {R K : Type*} [CommRing R] [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u})
    (τ : R →ₐ[K] R)
    (hres : ∀ v, PowerSeries.constantCoeff (ι (τ v)) = PowerSeries.constantCoeff (ι v)) :
    ∀ v, PowerSeries.coeff 1 (ι (τ v)) =
      PowerSeries.coeff 1 (ι (τ u)) * PowerSeries.coeff 1 (ι v) := by
  have hc (k : K) : ι (algebraMap K R k) = PowerSeries.C k := ι.commutes k
  have hz : PowerSeries.constantCoeff (ι (τ u)) = 0 := by
    rw [hres, hu, PowerSeries.constantCoeff_X]
  intro v
  obtain ⟨k, w, hv⟩ := s2v_l1b_rotation_parameter_division
    (algebraMap K R) (PowerSeries.constantCoeff.comp ι.toRingHom)
    (fun k => by change PowerSeries.constantCoeff (ι (algebraMap K R k)) = k
                 rw [hc, PowerSeries.constantCoeff_C]) u hker v
  rw [hv]
  simp only [map_add, map_mul, τ.commutes, hc, hu,
    PowerSeries.coeff_C_of_ne_zero (by omega : (1 : ℕ) ≠ 0), zero_add, PowerSeries.coeff_one_mul,
    hz, mul_zero, add_zero, PowerSeries.coeff_one_X,
    PowerSeries.constantCoeff_X, one_mul]

  rw [hres]

/-- Periodicity of a parameter forces its tangent scalar to have the same
power equal to one. -/
theorem s2v_l1b_rotation_tangent_pow
    {R K : Type*} [CommRing R] [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u})
    (τ : R →ₐ[K] R)
    (hres : ∀ v, PowerSeries.constantCoeff (ι (τ v)) = PowerSeries.constantCoeff (ι v))
    (N : ℕ) (hperiod : τ^[N] u = u) :
    PowerSeries.coeff 1 (ι (τ u)) ^ N = 1 := by
  have ht := s2v_l1b_rotation_tangent_scalar ι u hu hker τ hres
  have hi (n : ℕ) : PowerSeries.coeff 1 (ι (τ^[n] u)) =
      PowerSeries.coeff 1 (ι (τ u)) ^ n := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, hu, PowerSeries.coeff_one_X, pow_zero]
    | succ n ih => rw [Function.iterate_succ_apply', ht, ih, pow_succ']
  simpa only [hperiod, hu, PowerSeries.coeff_one_X] using (hi N).symm

/-- A local scalar-preserving endomorphism preserves the split residue map. -/
theorem s2v_l1b_rotation_residue_invariant
    {R K : Type*} [CommRing R] [Field K] [Algebra K R]
    (ρ : R →+* K) [IsLocalHom ρ]
    (hc : ∀ k, ρ (algebraMap K R k) = k)
    (τ : R →ₐ[K] R) [IsLocalHom τ.toRingHom] :
    ∀ v, ρ (τ v) = ρ v := by
  intro v
  have hz : ρ (v - algebraMap K R (ρ v)) = 0 := by
    rw [map_sub, hc, sub_self]
  have hn : ¬ IsUnit (v - algebraMap K R (ρ v)) := by
    intro h
    have := h.map ρ
    rw [hz] at this
    exact not_isUnit_zero this
  have ht : ¬ IsUnit (ρ (τ (v - algebraMap K R (ρ v)))) :=
    fun h => hn (isUnit_of_map_unit τ.toRingHom _ (isUnit_of_map_unit ρ _ h))
  have he := not_not.mp (mt isUnit_iff_ne_zero.mpr ht)
  simpa only [map_sub, τ.commutes, hc, sub_eq_zero] using he

end HodgeLean.Foundations.Program
