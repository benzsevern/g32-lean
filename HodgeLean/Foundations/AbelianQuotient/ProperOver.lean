import HodgeLean.Foundations.AbelianQuotient.ImageVarietyGeometry

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.AbelianQuotient

/-- A map over the base from a proper object to a separated object is proper. -/
theorem proper_over_map {Y Z : Over (Spec ↧ℂ)} [IsProper Y.hom] [IsSeparated Z.hom]
    (g : Y ⟶ Z) : IsProper g.left := by
  haveI : IsProper (g.left ≫ Z.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp g.left Z.hom

end HodgeLean.Foundations.AbelianQuotient
