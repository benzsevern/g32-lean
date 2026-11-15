import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Passing from a section ring to its fraction field does not change the subfield generated with a fixed element. -/
theorem s2v_l1b_fraction_field_generator
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra F K]
    (t : K) :
    Subfield.closure
        (Set.range ((algebraMap F K).comp (algebraMap R F)) ∪ {t}) =
      (IntermediateField.adjoin F {t}).toSubfield := by
  change Subfield.closure _ = Subfield.closure _
  apply le_antisymm
  · apply Subfield.closure_mono
    rintro x (⟨r, rfl⟩ | hx)
    · exact Or.inl ⟨algebraMap R F r, rfl⟩
    · exact Or.inr hx
  · apply Subfield.closure_le.mpr
    rintro x (⟨f, rfl⟩ | hx)
    · obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R f
      rw [map_div₀]
      exact Subfield.div_mem _
        (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
    · exact Subfield.subset_closure (Or.inr hx)

/-- A finite cyclic Galois extension has a nonzero binomial generator, expressed using the section ring image. -/
theorem s2v_l1b_cyclic_section_generator
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [IsCyclic (K ≃ₐ[F] K)]
    (hroots : (primitiveRoots (Module.finrank F K) F).Nonempty) :
    ∃ t : K, t ≠ 0 ∧
      Subfield.closure
        (Set.range ((algebraMap F K).comp (algebraMap R F)) ∪ {t}) = ⊤ ∧
      t ^ Module.finrank F K ∈ Set.range (algebraMap F K) := by
  obtain ⟨t, hpow, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic F K hroots
  have assemble : ∀ z : K, z ≠ 0 → IntermediateField.adjoin F {z} = ⊤ →
      z ^ Module.finrank F K ∈ Set.range (algebraMap F K) →
      ∃ t : K, t ≠ 0 ∧
        Subfield.closure
          (Set.range ((algebraMap F K).comp (algebraMap R F)) ∪ {t}) = ⊤ ∧
        t ^ Module.finrank F K ∈ Set.range (algebraMap F K) := by
    intro z hne hz hp
    refine ⟨z, hne, ?_, hp⟩
    rw [s2v_l1b_fraction_field_generator, hz]
    rfl
  by_cases ht : t = 0
  · subst t
    apply assemble 1 one_ne_zero
    · rw [IntermediateField.adjoin_one, ← (IntermediateField.adjoin_zero : IntermediateField.adjoin F {(0 : K)} = ⊥)]
      exact hgen
    · exact ⟨1, by simp only [map_one, one_pow]⟩
  · exact assemble t ht hgen hpow

end HodgeLean.Foundations.Program
