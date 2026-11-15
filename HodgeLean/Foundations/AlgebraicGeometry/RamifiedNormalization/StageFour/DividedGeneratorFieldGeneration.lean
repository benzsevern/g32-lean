import Mathlib.Algebra.Field.Subfield.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Removing the nonzero exceptional factor retains generation of the same original covering field over the actual chart coefficients. -/
theorem divided_generator_field_generation
    {A B K : Type*} [CommRing A] [CommRing B] [Field K]
    (F : A →+* K) (G : B →+* K) (j : A →+* B) (hcomp : G.comp j = F)
    (t : K) (v : A) (hv : F v ≠ 0)
    (hgen : Subfield.closure (Set.range F ∪ {t}) = ⊤) :
    Subfield.closure (Set.range G ∪ {t / F v}) = ⊤ := by
  let T := Subfield.closure (Set.range G ∪ {t / F v})
  have hF (a : A) : F a ∈ T := by
    apply Subfield.subset_closure
    exact Or.inl ⟨j a, congrArg (fun f : A →+* K => f a) hcomp⟩
  have hdiv : t / F v ∈ T := Subfield.subset_closure (Or.inr rfl)
  have ht : t ∈ T := by
    have h := T.mul_mem hdiv (hF v)
    rw [div_mul_cancel₀ _ hv] at h
    exact h
  have hle : Subfield.closure (Set.range F ∪ {t}) ≤ T := by
    apply Subfield.closure_le.mpr
    rintro z (hz | hz)
    · obtain ⟨a, rfl⟩ := hz
      exact hF a
    · rw [Set.mem_singleton_iff.mp hz]
      exact ht
  rw [hgen] at hle
  exact top_le_iff.mp hle

end AlgebraicGeometry.RamifiedNormalization.StageFour
