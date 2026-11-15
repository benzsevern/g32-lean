import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A surjective endomorphism of a Noetherian commutative ring is injective by stabilization of its actual iterated kernels.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 7. -/
theorem s2e_noetherian_ring_endomorphism_injective
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal R :=
    { toFun := fun n => RingHom.ker (f ^ n)
      monotone' := monotone_nat_of_le_succ (by
        intro n x hx
        change (f ^ (n + 1)) x = 0
        rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
        rw [RingHom.mem_ker.mp hx, map_zero]) }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  have hK : K n = K (n + 1) := hn (n + 1) (Nat.le_succ n)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := hf.iterate n x
  have hyK : y ∈ K (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    change f ((f^[n]) y) = 0
    rw [hy, hx]
  have hyK' : y ∈ K n := hK.symm ▸ hyK
  change (f^[n]) y = 0 at hyK'
  rwa [hy] at hyK'

#print axioms s2e_noetherian_ring_endomorphism_injective
end HodgeLean.Foundations.Program
