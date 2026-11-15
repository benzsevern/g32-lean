import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualChartFibre

/-! # The diagonal marked fibre in normalized residual coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation at a specified scalar gives the fibre ideal of a polynomial parameter. -/
theorem residual_polynomial_value_isPullback
    (R S : Type) [CommRing R] [CommRing S] (c : R →+* S) (t : S) (a : R) :
    let q := Ideal.Quotient.mk (Ideal.span {t - c a})
    IsPullback (Spec.map (CommRingCat.ofHom (q.comp c)))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom c t))) := by
  let q := Ideal.Quotient.mk (Ideal.span {t - c a})
  have ht : q t = q (c a) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hs : CommRingCat.ofHom (Polynomial.eval₂RingHom c t) ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Polynomial.evalRingHom a) ≫ CommRingCat.ofHom (q.comp c) := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simpa using ht
  have hk : (RingHom.ker (Polynomial.evalRingHom a)).map
      (Polynomial.eval₂RingHom c t) = RingHom.ker q := by
    rw [Ideal.mk_ker, Polynomial.ker_evalRingHom]
    simp only [Ideal.map_span, Set.image_singleton, Polynomial.eval₂_sub,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C]
  exact (residual_surjective_isPushout _ _ _ _ hs
    (Polynomial.eval_surjective a) Ideal.Quotient.mk_surjective hk).op.map Scheme.Spec

/-- The slice meets the residual chart at normalized ratio one. Translating
that ratio by one gives a parameter whose origin is the slice fibre.
Source: Hartshorne, Algebraic Geometry, II.7.13; Schoen,
Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_residual_chart_normalized_marked_fibre
    (A : Type) [CommRing A] (u v : A) (J : Ideal A) (α : (A ⧸ J)ˣ) :
    let B := ring u v ⧸ J.map (coeff u v)
    let c := pairedC3ResidualChartBase u v J
    let t : B := Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)
    let z := c (↑α⁻¹) * t
    let q := Ideal.Quotient.mk (Ideal.span {z - 1})
    IsPullback (Spec.map (CommRingCat.ofHom (q.comp c)))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : A ⧸ J))))
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom c z))) := by
  have h := residual_polynomial_value_isPullback
    (A ⧸ J) _ (pairedC3ResidualChartBase u v J)
    (pairedC3ResidualChartBase u v J (↑α⁻¹) *
      Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)) 1
  dsimp only at h ⊢
  rw [map_one] at h
  exact h

#print axioms residual_polynomial_value_isPullback
#print axioms pairedC3_residual_chart_normalized_marked_fibre
end HodgeLean.Foundations.Program.G32Native
