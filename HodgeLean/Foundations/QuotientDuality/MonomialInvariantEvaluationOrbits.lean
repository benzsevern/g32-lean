import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic

/-! Field-valued evaluation fibers of an explicit invariant presentation. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem invariant_presentation_evaluation_orbits
    {k N A G : Type*} [Field k] [CommRing N] [CommRing A] [Algebra k A]
    [Group G] [Finite G]
    (ρ : G →* (A ≃ₐ[k] A)) (β : N →+* A)
    (hfixed : ∀ a : A, (∃ b, β b = a) ↔ ∀ g, ρ g a = a)
    (φ ψ : A →ₐ[k] k) (heq : ∀ b, φ (β b) = ψ (β b)) :
    ∃ g : G, ∀ a, ψ a = φ (ρ g a) := by
  letI : MulSemiringAction G A := MulSemiringAction.compHom A ρ
  letI : SMulCommClass G k A := ⟨fun g x y => by
    change ρ g (x • y) = x • ρ g y
    exact (ρ g).toLinearEquiv.map_smul x y⟩
  by_contra hno
  obtain ⟨a, ha, hne⟩ :=
    HodgeLean.Foundations.Program.s2e_invariant_separates_evaluation_orbits φ ψ hno
  obtain ⟨b, rfl⟩ := (hfixed a).mpr ha
  exact hne (heq b)

#print axioms invariant_presentation_evaluation_orbits
end HodgeLean.Foundations.QuotientDuality
