import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Division

/-! # Polynomial insertion calculations for L1a

Implication from a polynomial parameter model to its coordinate insertion kernel.
Identification with the retained scheme insertion remains separate.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Setting one ordered parameter to zero has precisely its principal ideal as kernel.
Source: Hartshorne, Algebraic Geometry, II.2, coordinate hyperplanes. -/
theorem s2v_l1a_coordinate_insertion_kernel
    {R σ : Type*} [CommRing R] [DecidableEq σ] (i : σ) :
    RingHom.ker (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial σ R)
      (fun j => if j = i then 0 else MvPolynomial.X j)) =
      Ideal.span {MvPolynomial.X i} := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span {MvPolynomial.X i}
  let e := MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial σ R)
    (fun j => if j = i then 0 else MvPolynomial.X j)
  have hXi : (MvPolynomial.X i : MvPolynomial σ R) ∈ I :=
    Ideal.subset_span (Set.mem_singleton _)
  have he : (Ideal.Quotient.mk I).comp e = Ideal.Quotient.mk I := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, e, MvPolynomial.eval₂Hom_C]
    · intro j
      simp only [RingHom.comp_apply, e, MvPolynomial.eval₂Hom_X']
      split_ifs with hj
      · subst j
        simpa only [map_zero] using (Ideal.Quotient.eq_zero_iff_mem.mpr hXi).symm
      · rfl
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hp' : e p = 0 := hp
    have := DFunLike.congr_fun he p
    change Ideal.Quotient.mk I (e p) = Ideal.Quotient.mk I p at this
    rw [hp', map_zero] at this
    exact this.symm
  · apply Ideal.span_le.mpr
    rintro p rfl
    change e (MvPolynomial.X i) = 0
    simp only [e, MvPolynomial.eval₂Hom_X', ite_true]

end HodgeLean.Foundations.Program
