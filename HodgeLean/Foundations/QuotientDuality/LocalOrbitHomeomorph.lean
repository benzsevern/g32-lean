import HodgeLean.Foundations.QuotientDuality.DeckDefs
import Mathlib.Topology.Homeomorph.Lemmas

/-! A compact orbit quotient with the specified fibres is the actual target space. -/
noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

theorem compact_orbit_quotient_homeomorph
    (G : Type) [Group G] (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [CompactSpace X] [T2Space Y]
    (q : X → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
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
  exact ⟨he.homeoOfEquivCompactToT2, fun _ => rfl⟩

#print axioms compact_orbit_quotient_homeomorph
end HodgeLean.Foundations.QuotientDuality
