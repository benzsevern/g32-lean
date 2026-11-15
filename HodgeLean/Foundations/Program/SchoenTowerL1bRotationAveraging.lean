import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A finite orbit sum extracts an exact eigenvector for a finite-order ring action. -/
theorem s2v_l1b_rotation_orbit_sum_eigen
    {R : Type*} [CommRing R] (τ : R →+* R) (ζ u : R) (N : ℕ)
    (hζ : τ ζ = ζ) (hζN : ζ ^ N = 1) (hu : τ^[N] u = u) :
    τ (∑ i ∈ Finset.range N, ζ ^ (N - 1 - i) * τ^[i] u) =
      ζ * (∑ i ∈ Finset.range N, ζ ^ (N - 1 - i) * τ^[i] u) := by
  cases N with
  | zero => simp
  | succ n =>
    have hleft :
        τ (∑ i ∈ Finset.range (n + 1), ζ ^ (n + 1 - 1 - i) * τ^[i] u) =
          (∑ i ∈ Finset.range n, ζ ^ (n - i) * τ^[i + 1] u) + u := by
      rw [map_sum, Finset.sum_range_succ]
      simp only [map_mul, map_pow, hζ]
      have hi (i : ℕ) : τ (τ^[i] u) = τ^[i + 1] u :=
        (Function.iterate_succ_apply' τ i u).symm
      simp only [hi, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, hu]
    have hright :
        ζ * (∑ i ∈ Finset.range (n + 1), ζ ^ (n + 1 - 1 - i) * τ^[i] u) =
          u + (∑ i ∈ Finset.range n, ζ ^ (n - i) * τ^[i + 1] u) := by
      rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
      have hs : (∑ i ∈ Finset.range n,
          ζ * (ζ ^ (n + 1 - 1 - (i + 1)) * τ^[i + 1] u)) =
          ∑ i ∈ Finset.range n, ζ ^ (n - i) * τ^[i + 1] u := by
        apply Finset.sum_congr rfl
        intro i hi
        have he : n - i = (n + 1 - 1 - (i + 1)) + 1 := by
          have := Finset.mem_range.mp hi
          omega
        rw [← mul_assoc, ← pow_succ', ← he]
      rw [hs]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, Function.iterate_zero, id_eq]
      rw [← mul_assoc, ← pow_succ', hζN, one_mul, add_comm]
    rw [hleft, hright, add_comm]

/-- The orbit sum retains the first-order coefficient of an eigenparameter,
up to its explicit nonzero normalization factor. -/
theorem s2v_l1b_rotation_orbit_sum_linear
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (τ : R →+* R) (ζ : K) (u : R) (N : ℕ)
    (q : R →ₗ[K] K)
    (hq : ∀ i < N, q (τ^[i] u) = ζ ^ i * q u) :
    q (∑ i ∈ Finset.range N,
        (algebraMap K R ζ) ^ (N - 1 - i) * τ^[i] u) =
      (N : K) * (ζ ^ (N - 1) * q u) := by
  rw [map_sum]
  have hs : (∑ i ∈ Finset.range N,
      q ((algebraMap K R ζ) ^ (N - 1 - i) * τ^[i] u)) =
      ∑ _i ∈ Finset.range N, ζ ^ (N - 1) * q u := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN := Finset.mem_range.mp hi
    rw [← map_pow, ← Algebra.smul_def, map_smul, hq i hiN]
    change ζ ^ (N - 1 - i) * (ζ ^ i * q u) = _
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Normalizing the finite orbit sum gives an exact eigenparameter with the
same first-order coefficient as the initial parameter. -/
theorem s2v_l1b_rotation_normalized_eigenparameter
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    (τ : R →+* R) (hτ : ∀ c : K, τ (algebraMap K R c) = algebraMap K R c)
    (ζ : K) (hζ : ζ ≠ 0) (u : R) (N : ℕ) (hN : 0 < N)
    (hζN : ζ ^ N = 1) (hu : τ^[N] u = u)
    (q : R →ₗ[K] K) (hq : ∀ i < N, q (τ^[i] u) = ζ ^ i * q u) :
    ∃ v : R, τ v = (algebraMap K R ζ) * v ∧ q v = q u := by
  let A := ∑ i ∈ Finset.range N,
    (algebraMap K R ζ) ^ (N - 1 - i) * τ^[i] u
  let c : K := ((N : K) * ζ ^ (N - 1))⁻¹
  have hc : (N : K) * ζ ^ (N - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) (pow_ne_zero _ hζ)
  refine ⟨c • A, ?_, ?_⟩
  · have he := s2v_l1b_rotation_orbit_sum_eigen τ (algebraMap K R ζ) u N
      (hτ ζ) (by rw [← map_pow, hζN, map_one]) hu
    simp only [Algebra.smul_def]
    rw [map_mul, hτ, he]
    ring
  · rw [map_smul]
    change c * q A = q u
    have he := s2v_l1b_rotation_orbit_sum_linear τ ζ u N q hq
    change q A = _ at he
    rw [he]
    calc
      c * ((N : K) * (ζ ^ (N - 1) * q u)) =
          (c * ((N : K) * ζ ^ (N - 1))) * q u := by ring
      _ = q u := by dsimp [c]; rw [inv_mul_cancel₀ hc, one_mul]

/-- A scalar action on a first-order linear functional suffices to construct
an exact eigenparameter retaining that functional. -/
theorem s2v_l1b_rotation_eigenparameter_of_tangent
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    (τ : R →+* R) (hτ : ∀ c : K, τ (algebraMap K R c) = algebraMap K R c)
    (ζ : K) (hζ : ζ ≠ 0) (u : R) (N : ℕ) (hN : 0 < N)
    (hζN : ζ ^ N = 1) (hu : τ^[N] u = u)
    (q : R →ₗ[K] K) (hq : ∀ v, q (τ v) = ζ * q v) :
    ∃ v : R, τ v = (algebraMap K R ζ) * v ∧ q v = q u := by
  apply s2v_l1b_rotation_normalized_eigenparameter τ hτ ζ hζ u N hN hζN hu q
  have hall (i : ℕ) : q (τ^[i] u) = ζ ^ i * q u := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [Function.iterate_succ_apply', hq, hi, pow_succ']
      ring
  exact fun i _ => hall i

end HodgeLean.Foundations.Program
