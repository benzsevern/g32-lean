import HodgeLean.Foundations.Program.SchoenCycleAffineLinearIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Eliminating the normalized projective coordinate -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Setting the normalized homogeneous coordinate to one leaves the polynomial ring in the other coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_normalizedPolynomialQuotientEquiv {σ R : Type*} [CommRing R] (i : σ) :
    (MvPolynomial σ R ⧸ Ideal.span ({X i - 1} : Set (MvPolynomial σ R))) ≃+*
      MvPolynomial {j : σ // j ≠ i} R := by
  classical
  let I := Ideal.span ({X i - 1} : Set (MvPolynomial σ R))
  let π := Ideal.Quotient.mk I
  let f : MvPolynomial σ R →+* MvPolynomial {j : σ // j ≠ i} R :=
    eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)
  let g : MvPolynomial {j : σ // j ≠ i} R →+* MvPolynomial σ R ⧸ I :=
    π.comp (rename (R := R) (fun j : {j : σ // j ≠ i} => j.val)).toRingHom
  have hf : I ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change f (X i - 1) = 0
    simp [f]
  let f' := Ideal.Quotient.lift I f hf
  apply RingEquiv.ofRingHom f' g
  · apply MvPolynomial.ringHom_ext
    · intro r
      simp [f', g, π, f]
    · intro j
      simp [f', g, π, f, j.property]
  · apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f', g, π, f]
    · intro j
      change g (f (X j)) = π (X j)
      by_cases h : j = i
      · subst j
        have hz : π (X i - 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        have hi : π (X i) = 1 := by simpa only [map_sub, map_one, sub_eq_zero] using hz
        simpa [f] using hi.symm
      · simp [f, h, g, π]

/-- The coordinate-elimination equivalence evaluates polynomial residue classes by setting the chosen variable to one.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_normalizedPolynomialQuotientEquiv_mk {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) :
    s2e_normalizedPolynomialQuotientEquiv (R := R) i
      (Ideal.Quotient.mk (Ideal.span ({X i - 1} : Set (MvPolynomial σ R))) p) =
      eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩) p := rfl

end HodgeLean.Foundations.Program
