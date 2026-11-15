import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # Finite synthesis under bijective semilinear transport -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- Bijective scalar and section transports preserve finite synthesis in
specified original generators. -/
theorem paired_c3_synthesis_bijective_transfer
    {R S M N σ : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] [Fintype σ]
    (φ : R →+* S) (hφ : Function.Bijective φ)
    (f : M →+ N) (hf : Function.Bijective f)
    (hsmul : ∀ (r : R) (x : M), f (r • x) = φ r • f x)
    (g : σ → M) (w : σ → N) (hgw : ∀ a, f (g a) = w a)
    (hw : Function.Bijective (fun c : σ → S => ∑ a, c a • w a)) :
    Function.Bijective (fun c : σ → R => ∑ a, c a • g a) := by
  let e := RingEquiv.ofBijective φ hφ
  have hc : Function.Bijective (fun c : σ → R => fun a => φ (c a)) :=
    (Equiv.piCongrRight (fun _ : σ => e.toEquiv)).bijective
  have heq : f ∘ (fun c : σ → R => ∑ a, c a • g a) =
      (fun c : σ → S => ∑ a, c a • w a) ∘ (fun c a => φ (c a)) := by
    funext c
    simp only [Function.comp_apply, map_sum, hsmul, hgw]
  apply (Function.Bijective.of_comp_iff' hf _).mp
  rw [heq]
  exact hw.comp hc

#print axioms paired_c3_synthesis_bijective_transfer
end HodgeLean.Foundations.Program.G32Native
