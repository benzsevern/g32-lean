import HodgeLean.Foundations.Program.SchoenTowerInvariantLifting
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Averaging is linear over the fixed subalgebra.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
def s2t_reynolds (K A G : Type*)
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A] :
    A →ₗ[FixedPoints.subalgebra K A G] FixedPoints.subalgebra K A G where
  toFun a := ⟨(Fintype.card G : K)⁻¹ • ∑ g : G, g • a, by
    intro h
    rw [smul_comm, Finset.smul_sum]
    simp only [smul_smul]
    exact congrArg (fun x : A => (Fintype.card G : K)⁻¹ • x)
      (Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => g • a))⟩
  map_add' a b := by
    apply Subtype.ext
    change (Fintype.card G : K)⁻¹ • ∑ g : G, g • (a + b) = _
    simp only [smul_add, Finset.sum_add_distrib, Subalgebra.coe_add]
  map_smul' r a := by
    apply Subtype.ext
    change (Fintype.card G : K)⁻¹ • ∑ g : G, g • ((r : A) * a) =
      (r : A) * ((Fintype.card G : K)⁻¹ • ∑ g : G, g • a)
    simp only [smul_mul', (FixedPoints.mem_subalgebra.mp r.property)]
    rw [← Finset.mul_sum]
    exact (Algebra.mul_smul_comm _ _ _).symm

/-- Averaging restricts to the identity on the fixed subalgebra. -/
theorem s2t_reynolds_fixed {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (a : FixedPoints.subalgebra K A G) : s2t_reynolds K A G (a : A) = a := by
  apply Subtype.ext
  change (Fintype.card G : K)⁻¹ • ∑ g : G, g • (a : A) = (a : A)
  simp only [(FixedPoints.mem_subalgebra.mp a.property), Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

/-- Extending an ideal to the acted-on algebra and contracting it recovers the ideal.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
theorem s2t_fixed_ideal_comap_map {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    (J.map (FixedPoints.subalgebra K A G).toSubring.subtype).comap
      (FixedPoints.subalgebra K A G).toSubring.subtype = J := by
  let R := FixedPoints.subalgebra K A G
  let P := s2t_reynolds K A G
  apply le_antisymm ?_ Ideal.le_comap_map
  intro r hr
  have hmem : (r : A) ∈ J.map R.toSubring.subtype := hr
  have havg : ∀ a : A, P (a * (r : A)) ∈ J := by
    generalize (r : A) = x at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro a
      have heq : P (a * (j : A)) = j * P a := by
        rw [mul_comm]
        exact P.map_smul j a
      change P (a * (j : A)) ∈ J
      rw [heq]
      exact J.mul_mem_right _ hj
    | zero =>
      intro a
      rw [mul_zero, map_zero]
      exact J.zero_mem
    | add x y hx hy ihx ihy =>
      intro a
      rw [mul_add, map_add]
      exact J.add_mem (ihx a) (ihy a)
    | smul c x hx ih =>
      intro a
      change P (a * (c * x)) ∈ J
      rw [← mul_assoc]
      exact ih (a * c)
  have h := havg 1
  rw [one_mul] at h
  change s2t_reynolds K A G (r : A) ∈ J at h
  rwa [s2t_reynolds_fixed] at h

/-- Averaging preserves an image that is already invariant under the source action. -/
theorem s2t_reynolds_map_of_fixed {K A B G : Type*}
    [Field K] [CharZero K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (f : A →ₐ[K] B) (a : A) (h : ∀ g : G, f (g • a) = f a) :
    f (s2t_reynolds K A G a : A) = f a := by
  change f ((Fintype.card G : K)⁻¹ • ∑ g : G, g • a) = f a
  rw [map_smul, map_sum]
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

end HodgeLean.Foundations.Program
