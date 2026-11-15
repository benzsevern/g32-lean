import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- A flat, essentially finite type, formally unramified algebra over a domain
embeds in its reduced generic fibre and is therefore reduced. -/
theorem s2v_l1b_reduced_of_flat_unramified
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A] :
    IsReduced A := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] A)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- Extension of a prime ideal along an étale algebra map is radical. -/
theorem s2v_l1b_etale_map_prime_radical
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (I : Ideal R) [I.IsPrime] :
    (I.map (algebraMap R A)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  have : IsReduced ((R ⧸ I) ⊗[R] A) :=
    s2v_l1b_reduced_of_flat_unramified (R ⧸ I) ((R ⧸ I) ⊗[R] A)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).injective

end HodgeLean.Foundations.Program
