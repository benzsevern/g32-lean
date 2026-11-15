import HodgeLean.Foundations.AbelianQuotient.MultiplicationSection

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- An abelian subvariety has an algebraic retraction up to positive multiplication. -/
theorem subvariety_retraction {A : Variety} (S : Subvariety A) :
    ∃ (N : ℕ) (r : Hom A S.B), 0 < N ∧
      S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom := by
  haveI : Mono S.inclusion.hom := Over.mono_of_mono_left S.inclusion.hom
  obtain ⟨N, r, hN, h⟩ := hom_inner_inverse S.inclusion
  refine ⟨N, r, hN, ?_⟩
  apply (cancel_mono S.inclusion.hom).mp
  rw [Category.assoc, h, multiplication_nat_hom, GrpObj.zpow_comp, Category.id_comp]

end HodgeLean.Foundations.AbelianQuotient
