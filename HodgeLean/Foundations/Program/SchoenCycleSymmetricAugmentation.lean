import HodgeLean.Foundations.Program.SchoenCycleElementaryIdeal
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # Symmetric polynomials with zero constant term -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Every positive elementary symmetric polynomial has zero constant term.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_constantCoeff_esymm_succ
    (R σ : Type*) [CommRing R] [Fintype σ] (j : ℕ) :
    constantCoeff (esymm σ R (j + 1)) = 0 := by
  classical
  simp only [esymm, map_sum, map_prod, constantCoeff_X]
  apply Finset.sum_eq_zero
  intro t ht
  have hcard : t.card = j + 1 := (Finset.mem_powersetCard.mp ht).2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  exact Finset.prod_eq_zero hi rfl

#print axioms s2e_constantCoeff_esymm_succ
/-- Substitution of the positive elementary symmetric polynomials preserves
the constant coefficient.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_constantCoeff_aeval_esymm
    (R : Type*) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin n) R) :
    constantCoeff (aeval (fun j : Fin n => esymm (Fin n) R (j.val + 1)) p) =
      constantCoeff p := by
  have he : (constantCoeff : MvPolynomial (Fin n) R →+* R).comp
      (aeval (fun j : Fin n => esymm (Fin n) R (j.val + 1))).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simp [s2e_constantCoeff_esymm_succ]
  exact congrArg (fun f : MvPolynomial (Fin n) R →+* R => f p) he

#print axioms s2e_constantCoeff_aeval_esymm
/-- A symmetric polynomial with zero constant coefficient belongs to the
positive elementary symmetric ideal.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2,
the fundamental theorem of symmetric polynomials. -/
theorem s2e_symmetric_zero_constant_mem_elementary_ideal
    (R : Type*) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin n) R)
    (hp : IsSymmetric p) (h0 : constantCoeff p = 0) :
    p ∈ Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1))) := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective R (σ := Fin n) (n := n) (by simp) ⟨p, hp⟩
  have hqe : aeval (fun j : Fin n => esymm (Fin n) R (j.val + 1)) q = p := by
    simpa only [esymmAlgHom_apply] using congrArg (fun z : symmetricSubalgebra (Fin n) R => (z : MvPolynomial (Fin n) R)) hq
  have hq0 : constantCoeff q = 0 := by
    rw [← s2e_constantCoeff_aeval_esymm R n q, hqe, h0]
  let J : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1)))
  let π := Ideal.Quotient.mk J
  have he (j : Fin n) : π (esymm (Fin n) R (j.val + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hh : π.comp (aeval (fun j : Fin n => esymm (Fin n) R (j.val + 1))).toRingHom =
      (π.comp C).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simpa using he j
  have hv := congrArg (fun f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R ⧸ J => f q) hh
  change π (aeval (fun j : Fin n => esymm (Fin n) R (j.val + 1)) q) = π (C (constantCoeff q)) at hv
  rw [hqe, hq0, map_zero, map_zero] at hv
  exact Ideal.Quotient.eq_zero_iff_mem.mp hv

#print axioms s2e_symmetric_zero_constant_mem_elementary_ideal
end HodgeLean.Foundations.Program
