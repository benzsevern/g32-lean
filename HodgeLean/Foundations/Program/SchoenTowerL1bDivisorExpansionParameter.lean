import HodgeLean.Foundations.Program.SchoenTowerL1bTransportDvrOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A scalar-preserving DVR expansion containing X contains an actual uniformizer mapping to X. -/
theorem s2v_l1b_divisor_expansion_parameter
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (ι : R →+* PowerSeries K) (j : K →+* R)
    (hc : ∀ c, ι (j c) = PowerSeries.C c)
    (hX : ∃ t, ι t = PowerSeries.X) :
    ∃ t : R, Irreducible t ∧ ι t = PowerSeries.X := by
  let ρ := PowerSeries.constantCoeff.comp ι
  have hρ : Function.Surjective ρ := by
    intro c
    refine ⟨j c, ?_⟩
    change PowerSeries.constantCoeff (ι (j c)) = c
    rw [hc, PowerSeries.constantCoeff_C]
  letI : IsLocalHom ρ := IsLocalHom.of_surjective ρ hρ
  letI : IsLocalHom ι := isLocalHom_of_comp ι PowerSeries.constantCoeff
  obtain ⟨t, ht⟩ := hX
  exact ⟨t, Irreducible.of_map (f := ι) (by rw [ht]; exact PowerSeries.X_irreducible), ht⟩

end HodgeLean.Foundations.Program
