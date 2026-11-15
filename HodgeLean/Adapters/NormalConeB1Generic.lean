import HodgeLean.Adapters.NormalConeB1Polynomial

noncomputable section
namespace HodgeLean.Adapters

open LaurentPolynomial

def a3b1_laurentAlgebra (R : Type*) [CommRing R] (I : Ideal R) :
    Algebra (a3cc3_deformationAlgebra I) (LaurentPolynomial R) :=
  (a3cc3_deformationAlgebra I).val.toRingHom.toAlgebra

lemma a3b1_laurent_isLocalization
    (R : Type*) [CommRing R] (I : Ideal R) :
    letI := a3b1_laurentAlgebra R I
    IsLocalization.Away (a3cc3_parameter I) (LaurentPolynomial R) := by
  letI := a3b1_laurentAlgebra R I
  apply IsLocalization.Away.mk (a3cc3_parameter I)
  · change IsUnit (T (1 : ℤ) : LaurentPolynomial R)
    exact isUnit_T 1
  · intro f
    obtain ⟨n, g, hg⟩ := a3cc3_deformation_clear_denominators I f
    refine ⟨n, g, ?_⟩
    change f * T (1 : ℤ) ^ n = (g : LaurentPolynomial R)
    simpa only [T_pow, Int.mul_one] using hg
  · intro a b hab
    refine ⟨0, ?_⟩
    simp only [pow_zero, one_mul]
    apply Subtype.ext
    change (a : LaurentPolynomial R) = (b : LaurentPolynomial R) at hab
    exact hab

end HodgeLean.Adapters
