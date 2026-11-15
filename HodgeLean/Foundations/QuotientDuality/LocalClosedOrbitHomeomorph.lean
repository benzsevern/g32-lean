import HodgeLean.Foundations.QuotientDuality.LocalOrbitHomeomorph

/-! A closed quotient map with orbit fibres gives the actual orbit-space homeomorphism. -/
noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

theorem closed_orbit_quotient_homeomorph
    (G : Type) [Group G] (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X]
    (q : X → Y) (hq : Continuous q) (hqclosed : IsClosedMap q)
    (hsurj : Function.Surjective q)
    (hinv : ∀ (g : G) (x : X), q (g • x) = q x)
    (horbit : ∀ x y, q x = q y → ∃ g : G, g • x = y) :
    ∃ H : Quotient (MulAction.orbitRel G X) ≃ₜ Y,
      ∀ x, H (Quotient.mk _ x) = q x := by
  have hrel : ∀ x y, MulAction.orbitRel G X x y → q x = q y := by
    intro x y h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact hinv g y
  let φ : Quotient (MulAction.orbitRel G X) → Y := Quotient.lift q hrel
  have hbij : Function.Bijective φ := by
    constructor
    · intro u v
      induction u using Quotient.inductionOn with
      | h x =>
        induction v using Quotient.inductionOn with
        | h y =>
          intro hxy
          obtain ⟨g, hg⟩ := horbit x y hxy
          exact Quotient.sound ((MulAction.orbitRel G X).symm ⟨g, hg⟩)
    · intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨Quotient.mk _ x, rfl⟩
  let e := Equiv.ofBijective φ hbij
  have he : Continuous e := hq.quotient_lift hrel
  have hclosed : IsClosedMap e := by
    intro s hs
    have H := hqclosed ((Quotient.mk (MulAction.orbitRel G X)) ⁻¹' s)
      (hs.preimage continuous_quot_mk)
    convert H using 1
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective u
      exact ⟨x, hu, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Quotient.mk _ x, hx, rfl⟩
  exact ⟨e.toHomeomorphOfContinuousClosed he hclosed, fun _ => rfl⟩

#print axioms closed_orbit_quotient_homeomorph
end HodgeLean.Foundations.QuotientDuality
