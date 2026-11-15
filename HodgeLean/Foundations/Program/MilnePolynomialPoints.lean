import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

def m2_coordinatePoint {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] L) : σ → L :=
  fun i => φ (Ideal.Quotient.mkₐ K I (MvPolynomial.X i))

theorem m2_coordinatePoint_eval {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] L) :
    MvPolynomial.aeval (m2_coordinatePoint I φ) = φ.comp (Ideal.Quotient.mkₐ K I) := by
  ext i
  simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, m2_coordinatePoint]

theorem m2_coordinatePoint_mem_zeroLocus {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] L) :
    m2_coordinatePoint I φ ∈ MvPolynomial.zeroLocus L I := by
  intro p hp
  rw [m2_coordinatePoint_eval]
  change φ (Ideal.Quotient.mk I p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

def m2_quotientEval {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (x : σ → L) (hx : x ∈ MvPolynomial.zeroLocus L I) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] L :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (fun p hp => hx p hp)

theorem m2_quotientEval_coordinates {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (x : σ → L) (hx : x ∈ MvPolynomial.zeroLocus L I) :
    m2_coordinatePoint I (m2_quotientEval I x hx) = x := by
  funext i
  change MvPolynomial.aeval x (MvPolynomial.X i) = x i
  simp only [MvPolynomial.aeval_X]

end HodgeLean.Foundations.Program
