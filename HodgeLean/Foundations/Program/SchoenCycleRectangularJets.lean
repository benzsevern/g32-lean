import HodgeLean.Foundations.Program.SchoenCycleNilpotentCoordinateAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Truncated multivariable coordinate algebras -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The ideal cutting out the specified order in every polynomial coordinate.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_rectangularJetIdeal (σ : Type*) (N : ℕ) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ ℂ) ^ N)

/-- Scalar residue on the truncated multivariable coordinate algebra.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
def s2e_rectangularJetResidue (σ : Type*) (N : ℕ) (hN : 0 < N) :
    (MvPolynomial σ ℂ ⧸ s2e_rectangularJetIdeal σ N) →ₐ[ℂ] ℂ := by
  let ε : MvPolynomial σ ℂ →ₐ[ℂ] ℂ := aeval (fun _ : σ => (0 : ℂ))
  have hI : s2e_rectangularJetIdeal σ N ≤ RingHom.ker ε.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change ε (X i ^ N) = 0
    simp only [map_pow, ε, aeval_X, zero_pow (Nat.ne_of_gt hN)]
  exact Ideal.Quotient.liftₐ (s2e_rectangularJetIdeal σ N) ε (fun p hp => hI hp)

/-- Each coordinate of a truncated multivariable algebra has the specified
nilpotence order.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_rectangularJet_coordinate_nilpotent (σ : Type*) (N : ℕ) (i : σ) :
    IsNilpotent (Ideal.Quotient.mk (s2e_rectangularJetIdeal σ N) (X i)) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The scalar residue of a polynomial class is its constant coefficient.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_rectangularJetResidue_mk (σ : Type*) (N : ℕ) (hN : 0 < N)
    (p : MvPolynomial σ ℂ) :
    s2e_rectangularJetResidue σ N hN (Ideal.Quotient.mk (s2e_rectangularJetIdeal σ N) p) =
      constantCoeff p := by
  change aeval (fun _ : σ => (0 : ℂ)) p = constantCoeff p
  simp only [aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

/-- Truncated polynomial coordinates form a local complex algebra.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_rectangularJet_isLocalRing (σ : Type*) (N : ℕ) (hN : 0 < N) :
    IsLocalRing (MvPolynomial σ ℂ ⧸ s2e_rectangularJetIdeal σ N) := by
  let I := s2e_rectangularJetIdeal σ N
  let A := MvPolynomial σ ℂ ⧸ I
  let a : σ → A := fun i => Ideal.Quotient.mk I (X i)
  have ha (i : σ) : IsNilpotent (a i) := s2e_rectangularJet_coordinate_nilpotent σ N i
  have he : (aeval a : MvPolynomial σ ℂ →ₐ[ℂ] A) = Ideal.Quotient.mkₐ ℂ I := by
    ext i
    simp only [aeval_X]
    rfl
  apply s2e_nilpotent_scalar_residue_isLocalRing A (s2e_rectangularJetResidue σ N hN)
  intro r
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hp := s2e_nilpotent_coordinate_evaluation σ A a ha p
  rw [he] at hp
  rw [s2e_rectangularJetResidue_mk]
  exact hp

/-- For finitely many truncated coordinates, the maximal ideal is nilpotent.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 8 and 10. -/
theorem s2e_rectangularJet_maximalIdeal_nilpotent
    (σ : Type*) [Finite σ] (N : ℕ) (hN : 0 < N) :
    let A := MvPolynomial σ ℂ ⧸ s2e_rectangularJetIdeal σ N
    letI := s2e_rectangularJet_isLocalRing σ N hN
    IsNilpotent (IsLocalRing.maximalIdeal A) := by
  let I := s2e_rectangularJetIdeal σ N
  let A := MvPolynomial σ ℂ ⧸ I
  letI := s2e_rectangularJet_isLocalRing σ N hN
  let ε := s2e_rectangularJetResidue σ N hN
  letI : IsNoetherianRing A := inferInstance
  have hsurj : Function.Surjective ε := by
    intro c
    refine ⟨algebraMap ℂ A c, ?_⟩
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using ε.commutes c
  have hker := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hsurj
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).mpr
  intro r hr
  have hr0 : ε r = 0 := by
    change r ∈ RingHom.ker ε.toRingHom
    rwa [hker]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hp0 : constantCoeff p = 0 := (s2e_rectangularJetResidue_mk σ N hN p).symm.trans hr0
  let a : σ → A := fun i => Ideal.Quotient.mk I (X i)
  have he : (aeval a : MvPolynomial σ ℂ →ₐ[ℂ] A) = Ideal.Quotient.mkₐ ℂ I := by
    ext i
    simp only [aeval_X]
    rfl
  have hp := s2e_nilpotent_coordinate_evaluation σ A a
    (s2e_rectangularJet_coordinate_nilpotent σ N) p
  rw [he, hp0, map_zero, sub_zero] at hp
  exact mem_nilradical.mpr hp

end HodgeLean.Foundations.Program
