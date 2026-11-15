import HodgeLean.Foundations.AbelianQuotient.QuotientModel
import HodgeLean.Foundations.AbelianQuotient.MultiplicationFactors
import HodgeLean.Foundations.AbelianQuotient.QuotientKernel

noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The lattice image model gives an actual surjective projection with the prescribed point kernel. -/
theorem exists_quotient_geometry {A : Variety} (S : Subvariety A) :
    ∃ q : Projection S, Function.Surjective (Point.map q.map.hom) ∧
      {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
        Set.range (Point.map S.inclusion.hom) ∧
      ∃ ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice q.Q.X,
        Function.Surjective ψ ∧ ∀ x l,
          abelianPeriod A.X (homPullback q.map.hom 1 x) l = abelianPeriod q.Q.X x (ψ l) := by
  obtain ⟨N, r, hN, hr⟩ := subvariety_retraction S
  obtain ⟨B, i, q, hqi, hiq, ψ, hψs, hψ⟩ := difference_lattice_factorization S N r hr
  have hqs := surjective_of_multiplication_factor q i N hN hiq
  have hs := subvariety_comp_difference_factor S N hN r hr q i hqi hiq
  obtain ⟨I, hI⟩ := spec_abelianHom_analyticRepresentation S.inclusion.hom
  obtain ⟨Q, hQ⟩ := spec_abelianHom_analyticRepresentation q.hom
  have hker : ∀ v, Q v = 0 → v ∈ LinearMap.range I := by
    intro v hv
    exact kernel_of_difference_factor S N hN r q i hqi I Q hI hQ hv
  have hk := point_kernel_of_period_surjective S q hs I Q hI hQ ψ hψs hψ hker
  exact ⟨⟨B, q⟩, hqs, hk, ψ, hψs, hψ⟩

end HodgeLean.Foundations.AbelianQuotient
