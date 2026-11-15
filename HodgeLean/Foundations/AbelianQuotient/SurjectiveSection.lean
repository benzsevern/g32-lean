import HodgeLean.Foundations.AbelianQuotient.MultiplicationSection

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- Surjectivity turns a positive algebraic inner inverse into a multiplication section. -/
theorem exists_multiplication_section {A B : Variety} (f : Hom A B)
    (hs : Function.Surjective (Point.map f.hom)) :
    ∃ (N : ℕ) (s : Hom B A), 0 < N ∧
      s.hom ≫ f.hom = (multiplication B N).hom := by
  obtain ⟨N, s, hN, hh⟩ := hom_inner_inverse f
  refine ⟨N, s, hN, ?_⟩
  apply abq_over_hom_ext_of_point_map
  funext b
  obtain ⟨a, rfl⟩ := hs b
  change (a ≫ f.hom) ≫ (s.hom ≫ f.hom) =
    (a ≫ f.hom) ≫ (multiplication B N).hom
  rw [Category.assoc, multiplication_nat_hom, GrpObj.comp_zpow, Category.comp_id]
  have h := congrArg (fun t : A.X ⟶ B.X => a ≫ t) hh
  rw [GrpObj.comp_zpow] at h
  exact h

end HodgeLean.Foundations.AbelianQuotient
