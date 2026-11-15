import HodgeLean.Foundations.Program.SchoenCycleInvariantIdealJets

/-! # Contraction of invariant regular principal ideals -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Dividing two invariant elements by a regular invariant generator gives an invariant quotient, so its principal ideal contracts exactly.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_regular_principal_contraction
    {R A G : Type*} [CommRing R] [CommRing A] [Group G] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (φ : R →+* A)
    (hφ : Function.Injective φ)
    (hinv : ∀ g r, a g (φ r) = φ r)
    (hdesc : ∀ z : A, (∀ g, a g z = z) → ∃ r : R, φ r = z)
    (t : R) (ht : Function.Injective (fun z : A => φ t * z)) :
    Ideal.comap φ (Ideal.span {φ t}) = Ideal.span {t} := by
  apply le_antisymm
  · intro r hr
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hr
    have hzfix (g : G) : a g z = z := by
      apply ht
      calc
        φ t * a g z = a g (φ t * z) := by rw [map_mul, hinv]
        _ = φ r := by rw [← hz, hinv]
        _ = φ t * z := hz
    obtain ⟨s, hs⟩ := hdesc z hzfix
    apply Ideal.mem_span_singleton.mpr
    refine ⟨s, hφ ?_⟩
    rw [map_mul, hs]
    exact hz
  · apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact Ideal.subset_span rfl

end HodgeLean.Foundations.Program
