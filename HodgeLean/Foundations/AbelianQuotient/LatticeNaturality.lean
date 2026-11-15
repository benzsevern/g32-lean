import HodgeLean.Foundations.AbelianQuotient.Surjectivity

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The analytic representation agrees on periods with any map giving the pullback period square. -/
theorem analytic_lattice_map_eq {A B : Variety} (f : Hom A B)
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim B.X.left) → ℂ))
    (hQ : ∀ v, Additive.toMul (complexExponential B.X (dim B.X.left) (Q v)) =
      Point.map f.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    (ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice B.X)
    (hψ : ∀ x l, abelianPeriod A.X (homPullback f.hom 1 x) l =
      abelianPeriod B.X x (ψ l)) (l : abelianPeriodLattice A.X) :
    Q l = (ψ l : Fin (dim B.X.left) → ℂ) := by
  have h := lattice_eq_of_period B
    (a := ⟨Q l, homPullback_analyticRepresentation_mem_lattice f.hom Q hQ l⟩)
    (b := ψ l) ?_
  · exact congrArg Subtype.val h
  intro x
  rw [← abelianPeriod_homPullback_analyticRepresentation f.hom Q hQ]
  exact hψ x l

end HodgeLean.Foundations.AbelianQuotient
