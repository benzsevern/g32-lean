import HodgeLean.Foundations.Program.TorusAlgebraizationB54SectionPolynomial
import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalDescent
import HodgeLean.Foundations.Program.TorusAlgebraizationB54PolynomialScale

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.AnalyticDivisorAlgebraic2
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b54_factorEntire (l : Λ) : b54_thetaEntire Λ F :=
  ⟨b5_factor Λ F hF Q l, fun z => spec_analyticOnNhd_of_differentiableOn isOpen_univ
    (fun z _ => (b52_factor_hasFDerivAt Λ F hF Q l z).differentiableAt.differentiableWithinAt)
    z (Set.mem_univ z)⟩

def b54_thetaPolynomialTranslate (l : Λ) :
    Polynomial (b54_thetaEntire Λ F) →+* Polynomial (b54_thetaEntire Λ F) :=
  Polynomial.mapRingHom (b54_entireTranslate _ (b5_lattice Λ F l))

def b54_thetaPolynomialTwist (l : Λ) :
    Polynomial (b54_thetaEntire Λ F) →+* Polynomial (b54_thetaEntire Λ F) :=
  b54_polynomialScale (b54_factorEntire Λ F hF Q l ^ 3)

theorem b54_thetaPolynomialTranslate_injective (l : Λ) :
    Function.Injective (b54_thetaPolynomialTranslate Λ F l) :=
  Polynomial.map_injective _ (b54_entireTranslate_injective _ (b5_lattice Λ F l))

set_option backward.isDefEq.respectTransparency false in
theorem b54_thetaPolynomial_automorphy_iff (p : Polynomial (b54_thetaEntire Λ F)) :
    (∀ l, b54_thetaPolynomialTranslate Λ F l p = b54_thetaPolynomialTwist Λ F hF Q l p) ↔
      ∀ n l z, (p.coeff n).val (z + b5_lattice Λ F l) =
        b5_factor Λ F hF Q l z ^ (3 * n) * (p.coeff n).val z := by
  constructor
  · intro h n l z
    have hh := congrArg (fun q : Polynomial (b54_thetaEntire Λ F) => (q.coeff n).val z) (h l)
    simpa [b54_thetaPolynomialTranslate, b54_thetaPolynomialTwist,
      b54_polynomialScale_coeff, b54_entireTranslate, b54_factorEntire, pow_mul, add_comm] using hh
  · intro h l
    apply Polynomial.ext
    intro n
    apply Subtype.ext
    funext z
    simpa [b54_thetaPolynomialTranslate, b54_thetaPolynomialTwist,
      b54_polynomialScale_coeff, b54_entireTranslate, b54_factorEntire, pow_mul, add_comm] using h n l z

set_option backward.isDefEq.respectTransparency false in
theorem b54_sectionPolynomial_range (p : Polynomial (b54_thetaEntire Λ F)) :
    p ∈ (b54_sectionPolynomial Λ F hF Q).range ↔
      ∀ l, b54_thetaPolynomialTranslate Λ F l p = b54_thetaPolynomialTwist Λ F hF Q l p := by
  rw [b54_thetaPolynomial_automorphy_iff]
  constructor
  · rintro ⟨r, rfl⟩ n l z
    simp only [b54_sectionPolynomial_coeff]
    exact (r n).property.2 l z
  · intro h
    classical
    have hs (n : ℕ) : (p.coeff n).val ∈ b5_sections Λ F hF Q (3 * n) := by
      refine ⟨fun z => ((p.coeff n).property z).differentiableAt, h n⟩
    refine ⟨∑ n ∈ p.support, DirectSum.of _ n ⟨(p.coeff n).val, hs n⟩, ?_⟩
    rw [map_sum]
    calc
      _ = ∑ n ∈ p.support, Polynomial.monomial n (p.coeff n) := by
        apply Finset.sum_congr rfl
        intro n _
        simp [b54_sectionPolynomial, b54_sectionEntire]
      _ = p := Polynomial.sum_monomial_eq p

theorem b54_S_integrallyClosed : IsIntegrallyClosed (b5_S Λ F hF Q) := by
  letI := b54_S_isDomain Λ F hF Q
  letI := b54_entire_isDomain (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F))
  letI := b54_entire_integrallyClosed (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F))
  exact b54_normal_of_equalizer_range (b54_sectionPolynomial Λ F hF Q)
    (b54_sectionPolynomial_injective Λ F hF Q)
    (b54_thetaPolynomialTranslate Λ F) (b54_thetaPolynomialTwist Λ F hF Q)
    (b54_thetaPolynomialTranslate_injective Λ F)
    (b54_sectionPolynomial_range Λ F hF Q)

end HodgeLean.Foundations.Program
