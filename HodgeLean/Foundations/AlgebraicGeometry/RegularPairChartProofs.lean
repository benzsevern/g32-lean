import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartHelpers
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartTensor

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
namespace AlgebraicGeometry.RegularPairChart
open Polynomial

/-- A coefficient map and a solution of the relation determine exactly one chart map.
Source: Hartshorne, Algebraic Geometry, II.7; quotient-ring universal property. -/
theorem universal_aux {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) :
    ∃! φ : ring u v →+* A, φ.comp (coeff u v) = f ∧ φ (ratio u v) = s := by
  let J : Ideal R[X] := Ideal.span {C u - X * C v}
  have hJ : J ≤ RingHom.ker (eval₂RingHom f s) := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change (C u - X * C v).eval₂ f s = 0
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, hs, sub_self]
  let φ : ring u v →+* A := Ideal.Quotient.lift J (eval₂RingHom f s) (fun p hp => hJ hp)
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · ext r
    exact eval₂_C _ _
  · exact eval₂_X _ _
  · intro ψ hψ
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext'
    · exact hψ.1.trans (by ext r; exact (eval₂_C _ _).symm)
    · exact hψ.2.trans (eval₂_X _ _).symm

/-- The image of the two-generator centre has the denominator as generator.
Source: Hartshorne, Algebraic Geometry, II.7, affine blowup charts. -/
theorem centre_principal_aux {R : Type*} [CommRing R] (u v : R) :
    Ideal.span {coeff u v u, coeff u v v} = Ideal.span {coeff u v v} := by
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  have hrel : q (C u) = q X * q (C v) := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply Ideal.span_pair_eq_span_right_iff_dvd.mpr
  exact ⟨q X, hrel.trans (mul_comm _ _)⟩

/-- A regular pair yields a regular denominator in the quotient chart.
Source: Hartshorne, Algebraic Geometry, II.7; the cancellation argument in
SchoenTowerL1bChartRegularity, s2v_l1b_chart_relation_saturated. -/
theorem denominator_regular_aux {R : Type*} [CommRing R] (u v : R)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u)) :
    IsRegular (coeff u v v) := by
  exact quotient_denominator_regular u v hv hu

/-- Arbitrary coefficient extension preserves the chart and its two structure maps.
Source: Hartshorne, Algebraic Geometry, II.7; tensor quotient presentation in
SchoenTowerL1bChartTensor, s2v_l1b_chart_tensor_equiv. -/
theorem baseChangeEquiv_aux {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (u v : R) :
    ∃ e : (S ⊗[R] ring u v) ≃ₐ[S]
        ring (algebraMap R S u) (algebraMap R S v),
      (∀ s : S, e (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (B := ring u v) s) =
        coeff (algebraMap R S u) (algebraMap R S v) s) ∧
      e (Algebra.TensorProduct.includeRight (ratio u v)) =
        ratio (algebraMap R S u) (algebraMap R S v) := by
  obtain ⟨e, heC, heX⟩ := tensor_ring_equiv (A := S) u v
  let c := (Algebra.TensorProduct.comm R S (ring u v)).toRingEquiv
  let f := c.trans e
  have hf (s : S) : f (algebraMap S (S ⊗[R] ring u v) s) =
      algebraMap S (ring (algebraMap R S u) (algebraMap R S v)) s := by
    change e ((Algebra.TensorProduct.comm R S (ring u v)) (s ⊗ₜ[R] 1)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact heC s
  let ea := AlgEquiv.ofRingEquiv hf
  refine ⟨ea, ?_, ?_⟩
  · exact hf
  · change e ((Algebra.TensorProduct.comm R S (ring u v)) (1 ⊗ₜ[R] ratio u v)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact heX

/-- Distinct coordinates form a weakly regular sequence, preserved by flat extension.
Source: Matsumura, Commutative Ring Theory, §16, regular sequences and flatness;
SchoenTowerI2bCoordinateRegular, coordinate-list and flat-coordinate-list lemmas. -/
theorem coordinateSequence_of_flat_aux {κ R A : Type*} [CommRing R] [CommRing A]
    [Algebra (MvPolynomial κ R) A] [Module.Flat (MvPolynomial κ R) A]
    (l : List κ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial κ R)
        (l.map (MvPolynomial.X : κ → MvPolynomial κ R)) ∧
      RingTheory.Sequence.IsWeaklyRegular A
        (l.map (fun i => algebraMap (MvPolynomial κ R) A (MvPolynomial.X i))) := by
  exact ⟨coordinate_list_weakly_regular l hl, flat_coordinate_list_weakly_regular l hl⟩

end AlgebraicGeometry.RegularPairChart
