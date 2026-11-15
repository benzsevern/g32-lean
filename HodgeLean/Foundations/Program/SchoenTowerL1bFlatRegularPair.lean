import HodgeLean.Foundations.Program.SchoenTowerL1bChartRegularity
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Two distinct polynomial variables remain regular in succession. -/
theorem s2v_l1b_polynomial_coordinate_pair {k σ : Type*} [CommRing k] [IsDomain k]
    (i j : σ) (hij : i ≠ j) :
    IsRegular (MvPolynomial.X j : MvPolynomial σ k) ∧
      IsRegular (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X j}) (MvPolynomial.X i : MvPolynomial σ k)) := by
  refine ⟨MvPolynomial.isRegular_X, ?_⟩
  have : (Ideal.span {MvPolynomial.X j} : Ideal (MvPolynomial σ k)).IsPrime :=
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero j)).mpr MvPolynomial.X_prime
  apply IsRegular.of_ne_zero
  intro hz
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  exact hij (MvPolynomial.X_dvd_X.mp hd).symm

/-- The quotient used for a one-element module reduction agrees with the principal ideal quotient. -/
theorem s2v_l1b_quot_smul_top_equiv {R : Type*} [CommRing R] (v : R) :
    Nonempty (QuotSMulTop v R ≃ₗ[R] R ⧸ Ideal.span {v}) := by
  apply Nonempty.intro
  apply Submodule.quotEquivOfEq
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]

/-- A two-element weakly regular sequence is exactly regularity before and after the first quotient. -/
theorem s2v_l1b_weakly_regular_pair_iff {R : Type*} [CommRing R] (u v : R) :
    RingTheory.Sequence.IsWeaklyRegular R [v, u] ↔
      IsRegular v ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u) := by
  obtain ⟨e⟩ := s2v_l1b_quot_smul_top_equiv v
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff]
  simp only [RingTheory.Sequence.IsWeaklyRegular.nil, and_true]
  rw [e.isSMulRegular_congr u]
  have h₁ : IsSMulRegular R v ↔ IsRegular v :=
    (Commute.isRegular_iff (fun _ => Commute.all _ _)).symm
  have h₂ : IsSMulRegular (R ⧸ Ideal.span {v}) u ↔
      IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u) := by
    rw [Commute.isRegular_iff (fun _ => Commute.all _ _)]
    simp only [IsSMulRegular, IsLeftRegular, Algebra.smul_def]
    rfl
  exact and_congr h₁ h₂

/-- The regular-pair assumptions for a binomial chart survive flat base change. -/
theorem s2v_l1b_regular_pair_flat {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (u v : R)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u)) :
    IsRegular (algebraMap R A v) ∧
      IsRegular (Ideal.Quotient.mk (Ideal.span {algebraMap R A v}) (algebraMap R A u)) := by
  apply (s2v_l1b_weakly_regular_pair_iff _ _).mp
  have h := ((s2v_l1b_weakly_regular_pair_iff u v).mpr ⟨hv, hu⟩).of_flat (S := A)
  simpa only [List.map_cons, List.map_nil] using h

/-- Distinct coordinates of an étale polynomial map satisfy the regular-pair chart assumptions. -/
theorem s2v_l1b_etale_coordinate_pair {k R σ : Type*} [CommRing k] [IsDomain k] [CommRing R]
    (f : k →+* R) (z : σ → R) (het : (MvPolynomial.eval₂Hom f z).Etale)
    (i j : σ) (hij : i ≠ j) :
    IsRegular (z j) ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {z j}) (z i)) := by
  letI : Algebra (MvPolynomial σ k) R := (MvPolynomial.eval₂Hom f z).toAlgebra
  letI : Algebra.Etale (MvPolynomial σ k) R := het
  obtain ⟨hv, hu⟩ := s2v_l1b_polynomial_coordinate_pair (k := k) i j hij
  have h := s2v_l1b_regular_pair_flat (A := R) (MvPolynomial.X i) (MvPolynomial.X j) hv hu
  rw [show algebraMap (MvPolynomial σ k) R (MvPolynomial.X j) = z j from
    MvPolynomial.eval₂Hom_X' f z j,
    show algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) = z i from
    MvPolynomial.eval₂Hom_X' f z i] at h
  exact h

/-- The centre ideal has module trivializations on both charts of two distinct étale coordinates. -/
theorem s2v_l1b_etale_chart_trivializations {k R σ : Type*} [CommRing k] [IsDomain k] [CommRing R]
    (f : k →+* R) (z : σ → R) (het : (MvPolynomial.eval₂Hom f z).Etale)
    (i j : σ) (hij : i ≠ j) :
    let q₁ := Ideal.Quotient.mk (Ideal.span
      {Polynomial.C (z i) - Polynomial.X * Polynomial.C (z j)})
    let q₂ := Ideal.Quotient.mk (Ideal.span
      {Polynomial.C (z j) - Polynomial.X * Polynomial.C (z i)})
    Nonempty ((Ideal.span {q₁ (Polynomial.C (z i)), q₁ (Polynomial.C (z j))})
      ≃ₗ[s2v_L1bChart (z i) (z j)] s2v_L1bChart (z i) (z j)) ∧
    Nonempty ((Ideal.span {q₂ (Polynomial.C (z j)), q₂ (Polynomial.C (z i))})
      ≃ₗ[s2v_L1bChart (z j) (z i)] s2v_L1bChart (z j) (z i)) := by
  obtain ⟨hv, hu⟩ := s2v_l1b_etale_coordinate_pair f z het i j hij
  obtain ⟨hu', hv'⟩ := s2v_l1b_etale_coordinate_pair f z het j i hij.symm
  exact ⟨s2v_l1b_chart_centre_trivialization (z i) (z j) hv hu,
    s2v_l1b_chart_centre_trivialization (z j) (z i) hu' hv'⟩

end HodgeLean.Foundations.Program
