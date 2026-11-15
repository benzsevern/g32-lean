import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- An etale algebra over a domain embeds into its reduced generic fibre.
Source: Mathlib, `Algebra.FormallyUnramified.isReduced_of_field` and
`Algebra.TensorProduct.includeRight_injective`. -/
theorem s2v_i2a_etale_domain_reduced
    (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : IsReduced S := by
  let F := FractionRing R
  letI : IsReduced (F ⊗[R] S) :=
    Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[R] S)
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : S →ₐ[R] F ⊗[R] S)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R F))

/-- Extending a prime ideal through an etale algebra gives a radical ideal.
Source: Mathlib, `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and
`Ideal.isRadical_iff_quotient_reduced`. -/
theorem s2v_i2a_etale_prime_extension_radical
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (I : Ideal R) [I.IsPrime] : (I.map (algebraMap R S)).IsRadical := by
  letI : IsReduced ((R ⧸ I) ⊗[R] S) :=
    s2v_i2a_etale_domain_reduced (R ⧸ I) ((R ⧸ I) ⊗[R] S)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr
    (isReduced_of_injective e e.injective)

/-- Each actual polynomial coordinate remains a reduced principal divisor after
etale coefficient transport.
Source: Mathlib, `MvPolynomial.X_prime`, `Ideal.map_span` and
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. -/
theorem s2v_i2a_etale_coordinate_radical
    (A : Type*) [CommRing A] [IsDomain A] (ι : Type*)
    (S : Type*) [CommRing S] [Algebra (MvPolynomial ι A) S]
    [Algebra.Etale (MvPolynomial ι A) S] (i : ι) :
    (Ideal.span {algebraMap (MvPolynomial ι A) S (MvPolynomial.X i)}).IsRadical := by
  let I : Ideal (MvPolynomial ι A) := Ideal.span {MvPolynomial.X i}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  simpa only [I, Ideal.map_span, Set.image_singleton] using
    s2v_i2a_etale_prime_extension_radical (MvPolynomial ι A) S I

end HodgeLean.Foundations.Program
