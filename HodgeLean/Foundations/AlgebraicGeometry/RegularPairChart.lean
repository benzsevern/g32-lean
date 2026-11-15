import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartProofs

/-!
# Regular-pair quotient chart interface

This module specifies implication from explicit ring, regular-pair and flatness
inputs to universal mapping, principal-centre, denominator-regularity,
coefficient-extension and coordinate-sequence statements. It asserts no scheme
chart cover, overlap identification or comparison with a geometric Rees chart.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
namespace AlgebraicGeometry.RegularPairChart

/-- A coefficient map and a solution of the relation determine exactly one chart map.
Source: Hartshorne, Algebraic Geometry, II.7; quotient-ring universal property. -/
theorem universal {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) :
    ∃! φ : ring u v →+* A, φ.comp (coeff u v) = f ∧ φ (ratio u v) = s :=
  universal_aux u v f s hs

/-- The image of the two-generator centre has the denominator as generator.
Source: Hartshorne, Algebraic Geometry, II.7, affine blowup charts. -/
theorem centre_principal {R : Type*} [CommRing R] (u v : R) :
    Ideal.span {coeff u v u, coeff u v v} = Ideal.span {coeff u v v} :=
  centre_principal_aux u v

/-- A regular pair yields a regular denominator in the quotient chart.
Source: Hartshorne, Algebraic Geometry, II.7; the cancellation argument in
SchoenTowerL1bChartRegularity, s2v_l1b_chart_relation_saturated. -/
theorem denominator_regular {R : Type*} [CommRing R] (u v : R)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u)) :
    IsRegular (coeff u v v) :=
  denominator_regular_aux u v hv hu

/-- Arbitrary coefficient extension preserves the chart and its two structure maps.
Source: Hartshorne, Algebraic Geometry, II.7; tensor quotient presentation in
SchoenTowerL1bChartTensor, s2v_l1b_chart_tensor_equiv. -/
theorem baseChangeEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (u v : R) :
    ∃ e : (S ⊗[R] ring u v) ≃ₐ[S]
        ring (algebraMap R S u) (algebraMap R S v),
      (∀ s : S, e (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (B := ring u v) s) =
        coeff (algebraMap R S u) (algebraMap R S v) s) ∧
      e (Algebra.TensorProduct.includeRight (ratio u v)) =
        ratio (algebraMap R S u) (algebraMap R S v) :=
  baseChangeEquiv_aux u v

/-- Distinct coordinates form a weakly regular sequence, preserved by flat extension.
Source: Matsumura, Commutative Ring Theory, §16, regular sequences and flatness;
SchoenTowerI2bCoordinateRegular, coordinate-list and flat-coordinate-list lemmas. -/
theorem coordinateSequence_of_flat {κ R A : Type*} [CommRing R] [CommRing A]
    [Algebra (MvPolynomial κ R) A] [Module.Flat (MvPolynomial κ R) A]
    (l : List κ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial κ R)
        (l.map (MvPolynomial.X : κ → MvPolynomial κ R)) ∧
      RingTheory.Sequence.IsWeaklyRegular A
        (l.map (fun i => algebraMap (MvPolynomial κ R) A (MvPolynomial.X i))) :=
  coordinateSequence_of_flat_aux l hl

example {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) :
    ∃! φ : ring u v →+* A, φ.comp (coeff u v) = f ∧ φ (ratio u v) = s :=
  universal u v f s hs

example {R : Type*} [CommRing R] (u v : R) :
    Ideal.span {coeff u v u, coeff u v v} = Ideal.span {coeff u v v} :=
  centre_principal u v

example {R : Type*} [CommRing R] (u v : R)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u)) :
    IsRegular (coeff u v v) :=
  denominator_regular u v hv hu

example {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (u v : R) :
    ∃ e : (S ⊗[R] ring u v) ≃ₐ[S]
        ring (algebraMap R S u) (algebraMap R S v),
      (∀ s : S, e (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (B := ring u v) s) =
        coeff (algebraMap R S u) (algebraMap R S v) s) ∧
      e (Algebra.TensorProduct.includeRight (ratio u v)) =
        ratio (algebraMap R S u) (algebraMap R S v) :=
  baseChangeEquiv u v

example {κ R A : Type*} [CommRing R] [CommRing A]
    [Algebra (MvPolynomial κ R) A] [Module.Flat (MvPolynomial κ R) A]
    (l : List κ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial κ R)
        (l.map (MvPolynomial.X : κ → MvPolynomial κ R)) ∧
      RingTheory.Sequence.IsWeaklyRegular A
        (l.map (fun i => algebraMap (MvPolynomial κ R) A (MvPolynomial.X i))) :=
  coordinateSequence_of_flat l hl

end AlgebraicGeometry.RegularPairChart
