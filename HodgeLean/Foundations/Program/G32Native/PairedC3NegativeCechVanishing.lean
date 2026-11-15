import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistPositiveVanishing

/-! # The Laurent-monomial vanishing range needed by Route N -/
noncomputable section
set_option maxHeartbeats 400000
open Finset
open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech
open ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native

/-- Above degree −n−1, a Laurent monomial on P^n has at least one
nonnegative exponent.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1, monomial computation. -/
theorem paired_c3_negSupp_ne_univ {n : ℕ} (a : Twist.MonExp n)
    (ha : -(n + 1 : ℤ) < ∑ j, a j) :
    Twist.negSupp n a ≠ Finset.univ := by
  intro h
  have hle : ∀ j : Fin (n + 1), a j ≤ -1 := by
    intro j
    have hj : a j < 0 := (Twist.mem_negSupp n).mp (by
      rw [h]
      exact Finset.mem_univ j)
    omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) => hle j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Int.natCast_add, Int.natCast_one, mul_neg, mul_one] at hsum
  omega

#print axioms paired_c3_negSupp_ne_univ
/-- The top positive cohomology vanishes above the canonical degree.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_cech_top_vanishing
    (R : Type*) [CommRing R] (m : ℕ) (d : ℤ) (hd : -(m + 2 : ℤ) < d) :
    Subsingleton (Twist.H R (m + 1) d (m + 1)) := by
  let L : Twist.Sec R (m + 1) d (Idx.img (m + 1) (sfull (m := m))) →ₗ[R]
      Twist.cochain R (m + 1) d (m + 1) :=
    LinearMap.single R
      (fun s : Idx (m + 1) (m + 1) => Twist.Sec R (m + 1) d (Idx.img (m + 1) s))
      (sfull (m := m))
  have hmem : ∀ v : Twist.Sec R (m + 1) d (Idx.img (m + 1) (sfull (m := m))),
      L v ∈ LinearMap.range (Twist.d R (m + 1) d m) := by
    intro v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [map_add]
      exact Submodule.add_mem _ hv hw
    · intro b r
      have hb : Twist.negSupp (m + 1) b.val ≠ Finset.univ :=
        paired_c3_negSupp_ne_univ b.val (by rw [b.property.1]; exact_mod_cast hd)
      exact basis_mem_range R d b hb r
  change Subsingleton ((LinearMap.ker (Twist.d R (m + 1) d (m + 1))) ⧸
    (LinearMap.range (Twist.d R (m + 1) d m)).comap
      (LinearMap.ker (Twist.d R (m + 1) d (m + 1))).subtype)
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro f
  have hf : L (f.val (sfull (m := m))) = f.val := by
    funext s
    change Pi.single
      (M := fun t : Idx (m + 1) (m + 1) =>
        Twist.Sec R (m + 1) d (Idx.img (m + 1) t))
      (sfull (m := m)) (f.val (sfull (m := m))) s = f.val s
    rw [eq_sfull s, Pi.single_eq_same]
  change f.val ∈ LinearMap.range (Twist.d R (m + 1) d m)
  rw [← hf]
  exact hmem (f.val _)

#print axioms paired_c3_cech_top_vanishing
/-- All positive cohomology vanishes for twists above the canonical degree.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_cech_positive_vanishing
    (R : Type*) [CommRing R] (n : ℕ) (d : ℤ)
    (hd : -(n + 1 : ℤ) < d) (i : ℕ) :
    Subsingleton (Twist.H R n d (i + 1)) := by
  rcases lt_trichotomy (i + 1) n with hlt | heq | hgt
  · exact subsingleton_cohomology_succ_of_le R d (Nat.succ_le_iff.mpr hlt)
  · subst n
    exact paired_c3_cech_top_vanishing R i d (by omega)
  · exact subsingleton_cohomology_of_lt R n d hgt

#print axioms paired_c3_cech_positive_vanishing
end HodgeLean.Foundations.Program.G32Native
