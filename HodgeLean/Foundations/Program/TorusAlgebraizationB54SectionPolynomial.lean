import HodgeLean.Foundations.Program.TorusAlgebraizationB54Entire
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Domain
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Jets
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.AnalyticDivisorAlgebraic2
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

abbrev b54_thetaEntire := b54_entireRing (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F))

def b54_sectionEntire (n : ℕ) (s : b5_sections Λ F hF Q n) : b54_thetaEntire Λ F :=
  ⟨s.val, fun z => spec_analyticOnNhd_of_differentiableOn isOpen_univ
    s.property.1.differentiableOn z (Set.mem_univ z)⟩

set_option backward.isDefEq.respectTransparency false in
def b54_sectionPolynomial : b5_S Λ F hF Q →+* Polynomial (b54_thetaEntire Λ F) :=
  DirectSum.toSemiring
    (fun n => { toFun := fun s => Polynomial.monomial n (b54_sectionEntire Λ F hF Q (3 * n) s)
                map_zero' := by
                  change Polynomial.monomial n (0 : b54_thetaEntire Λ F) = 0
                  exact map_zero _
                map_add' := by
                  intro s t
                  change Polynomial.monomial n
                    (b54_sectionEntire Λ F hF Q (3 * n) s + b54_sectionEntire Λ F hF Q (3 * n) t) = _
                  exact map_add _ _ _ })
    (by
      change Polynomial.monomial 0 (1 : b54_thetaEntire Λ F) = 1
      simp)
    (by
      intro i j s t
      change Polynomial.monomial (i + j)
        (b54_sectionEntire Λ F hF Q (3 * i) s * b54_sectionEntire Λ F hF Q (3 * j) t) = _
      exact (Polynomial.monomial_mul_monomial _ _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in

theorem b54_sectionPolynomial_coeff (r : b5_S Λ F hF Q) (n : ℕ) :
    ((b54_sectionPolynomial Λ F hF Q r).coeff n).val = (r n).val := by
  classical
  induction r using DirectSum.induction_on with
  | zero => simp
  | of i s =>
    by_cases h : i = n
    · subst n
      simp [b54_sectionPolynomial, DirectSum.of_apply, b54_sectionEntire]
    · simp [b54_sectionPolynomial, DirectSum.of_apply, Polynomial.coeff_monomial, h]
  | add r s hr hs => simp [hr, hs]

theorem b54_sectionPolynomial_injective :
    Function.Injective (b54_sectionPolynomial Λ F hF Q) := by
  intro a b h
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  simpa only [b54_sectionPolynomial_coeff] using
    congrArg (fun p : Polynomial (b54_thetaEntire Λ F) => (p.coeff n).val) h

end HodgeLean.Foundations.Program
