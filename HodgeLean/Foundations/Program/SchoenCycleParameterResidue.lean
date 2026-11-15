import HodgeLean.Foundations.Program.SchoenCycleParameterJetMaps

/-! # Scalar reduction of finite parameter maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A parameter map with zero scalar parameter residue reduces to the original
residue map of the local algebra.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_parameter_map_scalar_reduction
    (R A : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    [CommRing A] [Algebra ℂ A] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (f : R →ₐ[ℂ] A) (ε : A →ₐ[ℂ] ℂ) (hε : ε (f t) = 0) :
    ε.comp f = φ := by
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨algebraMap ℂ R c, ?_⟩
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes c
  have hker := IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hsurj
  have ht0 : φ t = 0 := by
    change t ∈ RingHom.ker φ.toRingHom
    rw [hker, ht]
    exact Ideal.subset_span rfl
  apply s2e_parameter_nilpotent_map_ext R ℂ φ t ht 1 (ε.comp f) φ
  · simpa only [AlgHom.comp_apply, pow_one] using hε
  · exact hε.trans ht0.symm

end HodgeLean.Foundations.Program
