import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Ring

/-! # Finite expansions in a curve parameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A principal parameter with scalar residue representatives gives finite scalar
expansions to every order.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
expansion in powers of a parameter in a local ring. -/
theorem s2e_principal_parameter_jet_expansion
    (R : Type*) [CommRing R] [Algebra ℂ R] (t : R)
    (hscalar : ∀ r : R, ∃ c : ℂ, r - algebraMap ℂ R c ∈ Ideal.span {t})
    (N : ℕ) (r : R) :
    ∃ c : Fin N → ℂ,
      r - ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ) ∈ Ideal.span {t ^ N} := by
  classical
  induction N generalizing r with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp only [Fin.sum_univ_zero, sub_zero, pow_zero, Ideal.span_singleton_one]
    trivial
  | succ N ih =>
    obtain ⟨c₀, hc₀⟩ := hscalar r
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hc₀
    obtain ⟨c, hc⟩ := ih q
    refine ⟨Fin.cons c₀ c, ?_⟩
    have hsum :
        (∑ i : Fin (N + 1), algebraMap ℂ R (((Fin.cons c₀ c : Fin (N + 1) → ℂ) i)) * t ^ (i : ℕ)) =
          algebraMap ℂ R c₀ + t * ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hc
    apply Ideal.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    calc
      r - ∑ i : Fin (N + 1), algebraMap ℂ R (((Fin.cons c₀ c : Fin (N + 1) → ℂ) i)) * t ^ (i : ℕ) =
          t * (q - ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ)) := by
        rw [hsum, eq_add_of_sub_eq hq]
        ring
      _ = t * (t ^ N * s) := by rw [hs]
      _ = t ^ (N + 1) * s := by rw [pow_succ]; ring

/-- A complex residue evaluation supplies the scalar coefficients of each finite
expansion in a generator of the maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
expansion in a parameter with its residue field as coefficient field. -/
theorem s2e_local_parameter_jet_expansion
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (N : ℕ) (r : R) :
    ∃ c : Fin N → ℂ,
      r - ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ) ∈ Ideal.span {t ^ N} := by
  have hsurj : Function.Surjective φ := by
    intro c
    exact ⟨algebraMap ℂ R c, by simpa only [Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes c⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hsurj
  apply s2e_principal_parameter_jet_expansion R t ?_ N r
  intro s
  refine ⟨φ s, ?_⟩
  rw [← ht, ← hker, RingHom.mem_ker]
  change φ (s - algebraMap ℂ R (φ s)) = 0
  rw [map_sub, φ.commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self]

/-- Finite powers of a regular parameter are independent modulo the next power
when evaluated over the scalar residue field.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
uniqueness of parameter expansions. -/
theorem s2e_parameter_jet_coefficients_zero
    (R : Type*) [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : φ t = 0) (hreg : Function.Injective (fun x : R => t * x))
    (N : ℕ) (c : Fin N → ℂ)
    (h : (∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ)) ∈ Ideal.span {t ^ N}) :
    ∀ i, c i = 0 := by
  classical
  induction N with
  | zero => intro i; exact Fin.elim0 i
  | succ N ih =>
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp h
    have hsum :
        (∑ i : Fin (N + 1), algebraMap ℂ R (c i) * t ^ (i : ℕ)) =
          algebraMap ℂ R (c 0) + t * ∑ i : Fin N, algebraMap ℂ R (c i.succ) * t ^ (i : ℕ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    have hc0 : c 0 = 0 := by
      have he := congrArg φ hq
      rw [hsum] at he
      simpa only [map_add, map_mul, map_pow, φ.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, ht, zero_pow (Nat.succ_ne_zero N), zero_mul, add_zero] using he
    have htail : (∑ i : Fin N, algebraMap ℂ R (c i.succ) * t ^ (i : ℕ)) ∈
        Ideal.span {t ^ N} := by
      apply Ideal.mem_span_singleton.mpr
      refine ⟨q, hreg ?_⟩
      calc
        t * (∑ i : Fin N, algebraMap ℂ R (c i.succ) * t ^ (i : ℕ)) =
            ∑ i : Fin (N + 1), algebraMap ℂ R (c i) * t ^ (i : ℕ) := by
          rw [hsum, hc0, map_zero, zero_add]
        _ = t ^ (N + 1) * q := hq
        _ = t * (t ^ N * q) := by rw [pow_succ]; ring
    intro i
    exact Fin.cases hc0 (ih (fun j => c j.succ) htail) i

/-- In a regular local parameter, scalar expansions of every finite jet are unique.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
existence and uniqueness of parameter expansions. -/
theorem s2e_local_parameter_jet_expansion_unique
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) (N : ℕ) (r : R) :
    ∃! c : Fin N → ℂ,
      r - ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ) ∈ Ideal.span {t ^ N} := by
  obtain ⟨c, hc⟩ := s2e_local_parameter_jet_expansion R φ t ht N r
  refine ⟨c, hc, ?_⟩
  intro e he
  have hsurj : Function.Surjective φ := by
    intro z
    exact ⟨algebraMap ℂ R z, by simpa only [Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes z⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hsurj
  have ht0 : φ t = 0 := by
    change t ∈ RingHom.ker φ.toRingHom
    rw [hker, ht]
    exact Ideal.subset_span rfl
  have hdiff : (∑ i : Fin N, algebraMap ℂ R (e i - c i) * t ^ (i : ℕ)) ∈
      Ideal.span {t ^ N} := by
    have hsub := (Ideal.span {t ^ N}).sub_mem hc he
    convert hsub using 1
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hz := s2e_parameter_jet_coefficients_zero R φ t ht0 hreg N (fun i => e i - c i) hdiff
  funext i
  exact sub_eq_zero.mp (hz i)

end HodgeLean.Foundations.Program
