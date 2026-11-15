import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Injective quotient pullback identifies a primitive kernel with the character relations. -/
theorem s0_primitive_pullback_range
    {H Y V : Type*} [Group H] [AddCommGroup Y] [Module ℚ Y]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (χ : H →* Multiplicative (ZMod m)) (hχ : Function.Surjective χ)
    (R : H → Module.End ℚ V) (B : Module.End ℚ Y) (q : Y →ₗ[ℚ] V)
    (hq : Function.Injective q)
    (hr : LinearMap.range q = ⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id)
    (he : ∀ h, χ h = Multiplicative.ofAdd 1 → q ∘ₗ B = R h ∘ₗ q) :
    (LinearMap.ker (Polynomial.aeval B (Polynomial.cyclotomic m ℚ))).map q =
      (⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id) ⊓
        ⨅ h, ⨅ (_ : χ h = Multiplicative.ofAdd 1),
          LinearMap.ker (Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ)) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hr]
      exact LinearMap.mem_range_self q y
    · change q y ∈ ⨅ h, ⨅ (_ : χ h = Multiplicative.ofAdd 1),
        LinearMap.ker (Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ))
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro h hh
      have hp := LinearMap.congr_fun (g32y_aeval_intertwine q B (R h) (he h hh)
        (Polynomial.cyclotomic m ℚ)) y
      change Polynomial.aeval B (Polynomial.cyclotomic m ℚ) y = 0 at hy
      simpa only [LinearMap.comp_apply, hy, map_zero] using hp.symm
  · intro hv
    have hvq : v ∈ LinearMap.range q := by rw [hr]; exact hv.1
    obtain ⟨y, rfl⟩ := hvq
    refine ⟨y, ?_, rfl⟩
    apply hq
    obtain ⟨h, hh⟩ := hχ (Multiplicative.ofAdd 1)
    have hp := LinearMap.congr_fun (g32y_aeval_intertwine q B (R h) (he h hh)
      (Polynomial.cyclotomic m ℚ)) y
    have hz := ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv.2 h) hh)
    change Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ) (q y) = 0 at hz
    simpa only [LinearMap.comp_apply, hz, map_zero] using hp

#print axioms s0_primitive_pullback_range
end HodgeLean.Foundations.Program
