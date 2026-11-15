import HodgeLean.Foundations.Program.SchoenTowerL1bRotationResidueKernel

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A parameter in one normalized DVR expansion has nonzero linear coefficient
in every other normalized expansion. -/
theorem s2v_l1b_action_parameter_linear_ne_zero
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra K R]
    (φ ψ : R →ₐ[K] PowerSeries K) (u v : R)
    (hu : φ u = PowerSeries.X) (hv : ψ v = PowerSeries.X) :
    PowerSeries.coeff 1 (ψ u) ≠ 0 := by
  obtain ⟨hlφ, hkφ⟩ := s2v_l1b_rotation_expansion_residue_kernel φ u hu
  obtain ⟨hlψ, hkψ⟩ := s2v_l1b_rotation_expansion_residue_kernel ψ v hv
  haveI := hlφ
  haveI := hlψ
  have hnu : ¬ IsUnit u := by
    intro h
    have hm := h.map φ.toRingHom
    change IsUnit (φ u) at hm
    rw [hu] at hm
    exact PowerSeries.X_irreducible.not_isUnit hm
  have hnv : ¬ IsUnit v := by
    intro h
    have hm := h.map ψ.toRingHom
    change IsUnit (ψ v) at hm
    rw [hv] at hm
    exact PowerSeries.X_irreducible.not_isUnit hm
  have hzero : PowerSeries.constantCoeff (ψ u) = 0 := by
    by_contra hn
    exact hnu (isUnit_of_map_unit (PowerSeries.constantCoeff.comp ψ.toRingHom) u
      (isUnit_iff_ne_zero.mpr hn))
  have hvmem : v ∈ Ideal.span ({u} : Set R) := by
    rw [← hkφ]
    change PowerSeries.constantCoeff (φ v) = 0
    by_contra hn
    exact hnv (isUnit_of_map_unit (PowerSeries.constantCoeff.comp φ.toRingHom) v
      (isUnit_iff_ne_zero.mpr hn))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hvmem
  have hprod : PowerSeries.coeff 1 (ψ u) * PowerSeries.constantCoeff (ψ t) = 1 := by
    have he := congrArg (fun r => PowerSeries.coeff 1 (ψ r)) ht
    simpa only [map_mul, PowerSeries.coeff_one_mul, hzero, mul_zero, add_zero,
      hv, PowerSeries.coeff_one_X] using he.symm
  intro hz
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- The scalar of a finite action does not depend on its normalized DVR
expansion. Only the first expansion needs to be injective. -/
theorem s2v_l1b_action_character_independent
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra K R]
    (φ ψ : R →ₐ[K] PowerSeries K) (hφ : Function.Injective φ)
    (u v : R) (hu : φ u = PowerSeries.X) (hv : ψ v = PowerSeries.X)
    (τ : R →+* R) (ζ η : K)
    (hζ : ∀ r, φ (τ r) = PowerSeries.rescale ζ (φ r))
    (hη : ∀ r, ψ (τ r) = PowerSeries.rescale η (ψ r)) : ζ = η := by
  have heigen : τ u = algebraMap K R ζ * u := by
    apply hφ
    rw [hζ, hu, map_mul, φ.commutes, PowerSeries.algebraMap_eq,
      PowerSeries.rescale_X, hu]
  have he := congrArg (PowerSeries.coeff 1) (hη u)
  rw [heigen, map_mul, ψ.commutes, PowerSeries.algebraMap_eq,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_one] at he
  exact mul_right_cancel₀ (s2v_l1b_action_parameter_linear_ne_zero φ ψ u v hu hv) he

end HodgeLean.Foundations.Program
