import HodgeLean.Adapters.NormalConeProofs

/-! # Affine deformation to the normal cone: stage A3-B1

Implication from a field algebra to parameter flatness, and implication from
regularity of a sequence to its normal bundle presentation. The fibre maps
retain their generator normalization. Scheme gluing, analytic specialization,
and the supported cup comparison belong to later stages.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- Multiplication by every nonzero polynomial in the parameter is injective.
Source: Fulton, *Intersection Theory*, second edition, §5.1, affine extended Rees construction. -/
theorem a3b1_parameter_polynomial_injective
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R)
    (p : Polynomial k) (hp : p ≠ 0) :
    Function.Injective (fun d : a3cc3_deformationAlgebra I =>
      a3b1_parameterMap k R I p * d) :=
  a3b1_parameter_polynomial_injective_aux k R I p hp

example
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R)
    (p : Polynomial k) (hp : p ≠ 0) :
    Function.Injective (fun d : a3cc3_deformationAlgebra I =>
      a3b1_parameterMap k R I p * d) :=
  a3b1_parameter_polynomial_injective k R I p hp

/-- Flatness over the parameter line for an arbitrary algebra over a field.
Source: Fulton, *Intersection Theory*, second edition, §5.1; Stacks Project, Lemma 15.22.11 (tag 0549). -/
theorem a3b1_flat
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) :
    letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra I) :=
      (a3b1_parameterMap k R I).toAlgebra
    Module.Flat (Polynomial k) (a3cc3_deformationAlgebra I) :=
  a3b1_flat_aux k R I

example
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) :
    letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra I) :=
      (a3b1_parameterMap k R I).toAlgebra
    Module.Flat (Polynomial k) (a3cc3_deformationAlgebra I) :=
  a3b1_flat k R I

/-- The punctured deformation is the Laurent polynomial ring, extending its given inclusion.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
theorem a3b1_genericFiber (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : Localization.Away (a3cc3_parameter I) ≃+* LaurentPolynomial R,
      ∀ d : a3cc3_deformationAlgebra I,
        e (algebraMap _ (Localization.Away (a3cc3_parameter I)) d) =
          (d : LaurentPolynomial R) :=
  a3b1_genericFiber_aux R I

example (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : Localization.Away (a3cc3_parameter I) ≃+* LaurentPolynomial R,
      ∀ d : a3cc3_deformationAlgebra I,
        e (algebraMap _ (Localization.Away (a3cc3_parameter I)) d) =
          (d : LaurentPolynomial R) :=
  a3b1_genericFiber R I

/-- The zero fibre is the normal cone, preserving coefficients and the degree-one generators.
Source: Fulton, *Intersection Theory*, second edition, §§4.1 and 5.1, p. 88. -/
theorem a3b1_specialFiber (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : a3cc3_specialFiber I ≃ₐ[R] a3cc3_normalConeRing I,
      ∀ a : I, e (Ideal.Quotient.mk _ (a3b1_fractionGenerator R I a)) =
        a3b1_coneMonomial R I 1 ⟨a.val, by simpa only [pow_one] using a.property⟩ :=
  a3b1_specialFiber_aux R I

example (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : a3cc3_specialFiber I ≃ₐ[R] a3cc3_normalConeRing I,
      ∀ a : I, e (Ideal.Quotient.mk _ (a3b1_fractionGenerator R I a)) =
        a3b1_coneMonomial R I 1 ⟨a.val, by simpa only [pow_one] using a.property⟩ :=
  a3b1_specialFiber R I

/-- Implication from a regular sequence to the polynomial presentation of its normal cone.
Source: Stacks Project, Lemma 10.69.2 and Definition 10.69.1 (tag 061M). -/
theorem a3b1_regularSequence_normalBundle
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ e : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs) ≃ₐ[R]
        a3cc3_normalConeRing (Ideal.ofList rs),
      ∀ j : Fin rs.length, e (MvPolynomial.X j) =
        a3b1_coneMonomial R (Ideal.ofList rs) 1
          ⟨rs.get j, by
            rw [pow_one]
            exact Ideal.subset_span (List.get_mem rs j)⟩ :=
  a3b1_regularSequence_normalBundle_aux R rs hreg

example
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ e : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs) ≃ₐ[R]
        a3cc3_normalConeRing (Ideal.ofList rs),
      ∀ j : Fin rs.length, e (MvPolynomial.X j) =
        a3b1_coneMonomial R (Ideal.ofList rs) 1
          ⟨rs.get j, by
            rw [pow_one]
            exact Ideal.subset_span (List.get_mem rs j)⟩ :=
  a3b1_regularSequence_normalBundle R rs hreg

end HodgeLean.Adapters
