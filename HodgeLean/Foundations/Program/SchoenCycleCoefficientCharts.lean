import HodgeLean.Foundations.Program.SchoenCycleCoefficientDescent
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Scheme coefficient coordinates for the affine symmetric model -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The affine symmetric scheme has coefficient coordinates over any base ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2,
fundamental theorem of symmetric functions. -/
def s2e_affine_symmetric_coefficient_iso (R : Type) [CommRing R] (n : ℕ) :
    Spec (CommRingCat.of (symmetricSubalgebra (Fin n) R)) ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) R)) :=
  Scheme.Spec.mapIso
    (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).toRingEquiv.toCommRingCatIso.op

/-- Elementary coefficients determine points of the affine symmetric scheme over every algebra.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_symmetric_coefficient_hom_ext
    (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (f g : symmetricSubalgebra (Fin n) R →ₐ[R] A)
    (h : ∀ i : Fin n,
      f ⟨esymm (Fin n) R (i + 1), esymm_isSymmetric (Fin n) R _⟩ =
      g ⟨esymm (Fin n) R (i + 1), esymm_isSymmetric (Fin n) R _⟩) : f = g := by
  let e := esymmAlgEquiv (Fin n) R (Fintype.card_fin n)
  have he : f.comp e.toAlgHom = g.comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change f ((esymmAlgHom (Fin n) R n) (X i)) =
      g ((esymmAlgHom (Fin n) R n) (X i))
    simpa only [esymmAlgHom, aeval_X] using h i
  ext p
  obtain ⟨q, rfl⟩ := e.surjective p
  exact DFunLike.congr_fun he q

/-- The top elementary coefficient is the product of the root coordinates.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_top_elementary_coefficient
    (σ R : Type) [Fintype σ] [CommRing R] :
    esymm σ R (Fintype.card σ) = ∏ i : σ, (X i : MvPolynomial σ R) := by
  classical
  unfold esymm
  rw [← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]

end HodgeLean.Foundations.Program
