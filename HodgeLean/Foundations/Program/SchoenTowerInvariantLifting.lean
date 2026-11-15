import Mathlib.RingTheory.Invariant.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Field

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Surjective equivariant maps of characteristic-zero algebras are surjective on fixed
subalgebras, by averaging a lift.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
theorem s2t_fixedSubalgebra_lift {K A B G : Type*}
    [Field K] [CharZero K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Group G] [Fintype G] [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G K A] [SMulCommClass G K B]
    (f : A →ₐ[K] B) (hsurj : Function.Surjective f)
    (heq : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (b : FixedPoints.subalgebra K B G) :
    ∃ a : FixedPoints.subalgebra K A G, f a = (b : B) := by
  classical
  obtain ⟨a, ha⟩ := hsurj (b : B)
  let c : K := (Fintype.card G : K)⁻¹
  let t : A := ∑ g : G, g • a
  have ht (g : G) : g • t = t := by
    dsimp [t]
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => h • a)
  refine ⟨⟨c • t, ?_⟩, ?_⟩
  · rw [FixedPoints.mem_subalgebra]
    intro g
    rw [smul_comm, ht]
  · change f (c • t) = (b : B)
    rw [map_smul]
    have hft : f t = (Fintype.card G : K) • (b : B) := by
      dsimp [t]
      rw [map_sum]
      simp only [heq, ha, (FixedPoints.mem_subalgebra.mp b.property)]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [hft, smul_smul]
    have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [show c * (Fintype.card G : K) = 1 from inv_mul_cancel₀ hn, one_smul]

end HodgeLean.Foundations.Program
