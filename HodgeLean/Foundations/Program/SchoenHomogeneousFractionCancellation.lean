import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Equal homogeneous fractions with the same nonzero power denominator have equal numerators. -/
theorem s2_homogeneousAway_mk_num_injective {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] {a : A} {d : ℕ}
    (ha : a ∈ 𝒜 d) (hane : a ≠ 0) (n : ℕ) {b c : A}
    (hb : b ∈ 𝒜 (n • d)) (hc : c ∈ 𝒜 (n • d))
    (hbc : HomogeneousLocalization.Away.mk 𝒜 ha n b hb =
      HomogeneousLocalization.Away.mk 𝒜 ha n c hc) : b = c := by
  have he := congrArg HomogeneousLocalization.val hbc
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'] at he
  have hm := congrArg (fun z : Localization (Submonoid.powers a) =>
    z * algebraMap A (Localization (Submonoid.powers a)) (a ^ n)) he
  rw [IsLocalization.mk'_spec, IsLocalization.mk'_spec] at hm
  apply IsLocalization.injective (Localization (Submonoid.powers a)) (M := Submonoid.powers a) _ hm
  rintro _ ⟨k, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k hane)

end HodgeLean.Foundations.Program
