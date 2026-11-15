import HodgeLean.Foundations.Singular.ProductChains
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! Linear splittings of actual rational chain differentials. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- A rational-linear section of a chain differential onto its actual range.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient algebraic Künneth argument. -/
def rationalChainBoundarySection (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    LinearMap.range (K.d (n + 1) n).hom →ₗ[ℚ] K.X (n + 1) :=
  Classical.choose ((K.d (n + 1) n).hom.rangeRestrict.exists_rightInverse_of_surjective
    (K.d (n + 1) n).hom.range_rangeRestrict)

/-- The chosen rational section returns a primitive of each actual boundary.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient algebraic Künneth argument. -/
theorem rationalChainBoundarySection_boundary (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : LinearMap.range (K.d (n + 1) n).hom) :
    (K.d (n + 1) n).hom (rationalChainBoundarySection K n z) = z := by
  have h := LinearMap.congr_fun
    (Classical.choose_spec ((K.d (n + 1) n).hom.rangeRestrict.exists_rightInverse_of_surjective
      (K.d (n + 1) n).hom.range_rangeRestrict)) z
  exact congrArg Subtype.val h

#print axioms rationalChainBoundarySection
#print axioms rationalChainBoundarySection_boundary
end HodgeLean.Foundations.Singular
