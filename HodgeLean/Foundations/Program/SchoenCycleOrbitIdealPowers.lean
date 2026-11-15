import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Stabilizing the retained member of the ideal orbit preserves each of its actual powers.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_orbit_ideal_stabilizer_preserves_powers
    (G B : Type*) [Group G] [CommRing B] [MulSemiringAction G B]
    (I : Ideal B)
    (g : MulAction.stabilizer G (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit G I))
    (n : ℕ) (b : B) (hb : b ∈ I ^ n) : g.val • b ∈ I ^ n := by
  have hg : g.val • I = I := congrArg Subtype.val
    (show g.val • (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit G I) =
      (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit G I) from g.property)
  have h := Ideal.smul_mem_pointwise_smul g.val b (I ^ n) hb
  rwa [smul_pow', hg] at h

end HodgeLean.Foundations.Program
