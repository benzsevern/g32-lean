import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Reduced

/-! # Generic coefficients of étale inverse images

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

/-- Generic inverse-image stalks under an étale map have length one.
Source: Fulton, Intersection Theory, second edition, §1.7; reduced generic stalks. -/
theorem etale_genericLength_eq_one {X Z : Scheme} (f : X ⟶ Z) [Etale f]
    (x : Z) (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    ccm3_genericLength f x y = 1 := by
  haveI := inverseIdeal_isReduced f x
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents
    (ccm3_inverseIdeal f x).subscheme y hy
  letI := hfield.toField
  exact Module.length_eq_one _ _

/-- Each nonzero coefficient of an étale inverse-image prime cycle is one.
Source: Fulton, Intersection Theory, second edition, §1.7; ccm3_flatPullbackPrime_coeff. -/
theorem etale_prime_coefficient_one {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Etale f.left] (x : Z.left) (z : X.left)
    (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    ccm3_flatPullbackPrime f.left x z = 1 := by
  obtain ⟨y, rfl, hy⟩ := (ccm3_flatPullbackPrime_support f x z).mp hz
  rw [ccm3_flatPullbackPrime_coeff f x y hy, etale_genericLength_eq_one f.left x y hy]
  rfl

end AlgebraicGeometry.SingularCycles
