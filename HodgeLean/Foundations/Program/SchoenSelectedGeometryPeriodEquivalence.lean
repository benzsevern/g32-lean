import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodCharacter

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Rational period characters detect singular degree-one classes. -/
theorem s0_periodCharacter_injective : Function.Injective (s0_periodCharacter C) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply b3Rest2_eq_zero_of_T (Module.finrank_self ℂ)
  apply b3Rest2_eq_zero_of_re_lattice (Module.finrank_self ℂ)
  intro l
  have hp := s0_periodCharacter_spec C a l
  have hz : s0_periodCharacter C a l = 0 := congrArg (fun z : b3_periodLattice ℂ C →+ ℚ ↦ z l) ha
  rw [hz, Rat.cast_zero] at hp
  have hs : (b3Rest2_s : ℝ) ≠ 0 := by exact_mod_cast b3Rest2_s_ne_zero
  exact (mul_eq_zero.mp hp.symm).resolve_left hs

#print axioms s0_periodCharacter_injective

/-- Every rational character of the period lattice is represented by a singular class. -/
theorem s0_periodCharacter_bijective : Function.Bijective (s0_periodCharacter C) := by
  letI := b3_periodLattice_finite (C := C) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := C)
  let b := Module.finBasis ℤ (b3_periodLattice ℂ C)
  let e : (Fin (Module.finrank ℤ (b3_periodLattice ℂ C)) → ℚ) ≃ₗ[ℚ]
      (b3_periodLattice ℂ C →+ ℚ) :=
    (b.constr ℚ).trans (addMonoidHomLequivInt ℚ).symm
  letI : Module.Finite ℚ (b3_periodLattice ℂ C →+ ℚ) :=
    Module.Finite.of_injective e.symm.toLinearMap e.symm.injective
  letI := (b3Rest2_finrank_cohomology_le (C := C) (Module.finrank_self ℂ)).1
  have hd : Module.finrank ℚ (Cohomology ℚ (TopCat.of C) 1) =
      Module.finrank ℚ (b3_periodLattice ℂ C →+ ℚ) := by
    rw [← e.finrank_eq, Module.finrank_fin_fun,
      b3_finrank_periodLattice (Module.finrank_self ℂ),
      b3_finrank_cohomology (Module.finrank_self ℂ)]
  exact ⟨s0_periodCharacter_injective C,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (s0_periodCharacter_injective C)⟩

#print axioms s0_periodCharacter_bijective
end HodgeLean.Foundations.Program
