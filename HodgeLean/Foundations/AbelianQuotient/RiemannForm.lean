import HodgeLean.Foundations.Program.MilneFactorsHodgeSemisimple
import HodgeLean.Foundations.AbelianQuotient.Defs

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Projectivity supplies a positive integral Riemann form on the period lattice. -/
theorem exists_period_riemann_form (A : Variety) :
    ∃ Q : LinearMap.BilinForm ℤ (b2_abelianLattice A.X),
      b2_IsRiemannForm (b2_abelianLattice A.X) (b2_abelianF A.X) Q := by
  obtain ⟨D, hD⟩ := bh8_polarization A.X
  let Q : LinearMap.BilinForm ℤ (b2_abelianLattice A.X) :=
    LinearMap.mk₂ ℤ (fun l m => D.E l m)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  refine ⟨Q, ?_⟩
  apply (b2_abelian_isRiemannForm_iff A.X Q).mpr
  exact ⟨D.H, hD, D.integral⟩

end HodgeLean.Foundations.AbelianQuotient
