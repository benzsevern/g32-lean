import HodgeLean.Adapters.IntersectionProductCC3DeformationCore
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Affine normal cone coordinates

Reuse the extended Rees subalgebra and its two quotient rings from
`IntersectionProductCC3Deformation`. The constructions here use no theorem
from that module's open scaffold.
-/

noncomputable section
namespace HodgeLean.Adapters
open LaurentPolynomial

/-- The parameter-line structure map, with `X` sent to the actual parameter.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3b1_parameterMap (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    (I : Ideal R) : Polynomial k →+* a3cc3_deformationAlgebra I :=
  Polynomial.eval₂RingHom
    ((algebraMap R (a3cc3_deformationAlgebra I)).comp (algebraMap k R))
    (a3cc3_parameter I)

example (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) :
    a3b1_parameterMap k R I Polynomial.X = a3cc3_parameter I := by
  simp [a3b1_parameterMap]

/-- The generator `a/t`, for an actual element of the ideal.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b1_fractionGenerator (R : Type*) [CommRing R] (I : Ideal R) (a : I) :
    a3cc3_deformationAlgebra I :=
  ⟨C a.val * T (-1), Algebra.subset_adjoin
    (Set.mem_union_right _ ⟨a.val, a.property, rfl⟩)⟩

example (R : Type*) [CommRing R] (I : Ideal R) (a : I) :
    (a3b1_fractionGenerator R I a : LaurentPolynomial R) = C a.val * T (-1) := rfl

/-- A homogeneous class in the ordinary Rees quotient representing `I^n/I^(n+1)`.
Source: Fulton, *Intersection Theory*, second edition, §4.1; Mathlib,
`mem_map_algebraMap_reesAlgebra_iff`. -/
def a3b1_coneMonomial (R : Type*) [CommRing R] (I : Ideal R)
    (n : ℕ) (a : ↥(I ^ n)) : a3cc3_normalConeRing I :=
  Ideal.Quotient.mk _ ⟨Polynomial.monomial n a.val,
    reesAlgebra.monomial_mem.mpr a.property⟩

example (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) (a : ↥(I ^ n)) :
    a3b1_coneMonomial R I n a = Ideal.Quotient.mk _
      (⟨Polynomial.monomial n a.val, reesAlgebra.monomial_mem.mpr a.property⟩ :
        reesAlgebra I) := rfl

end HodgeLean.Adapters
