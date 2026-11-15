import HodgeLean.Foundations.AbelianQuotient.SubvarietyRetraction

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The difference between multiplication and the subvariety retraction composite. -/
def complementMap {A : Variety} (S : Subvariety A) (N : ℕ) (r : Hom A S.B) : Hom A A where
  hom := (multiplication A N).hom / (r.hom ≫ S.inclusion.hom)
  mon := by
    rw [div_eq_mul_inv, Hom.mul_def]
    infer_instance

set_option maxRecDepth 2000 in
/-- The retraction vanishes on the difference map. -/
theorem complement_map_comp_retraction {A : Variety} (S : Subvariety A)
    (N : ℕ) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom) :
    (complementMap S N r).hom ≫ r.hom = (1 : A.X ⟶ S.B.X) := by
  change ((multiplication A N).hom / (r.hom ≫ S.inclusion.hom)) ≫ r.hom = 1
  rw [GrpObj.div_comp, multiplication_nat_hom, GrpObj.zpow_comp, Category.id_comp,
    Category.assoc, hr, multiplication_nat_hom, GrpObj.comp_zpow, Category.comp_id]
  exact div_self' (r.hom ^ (N : ℤ))

set_option maxRecDepth 2000 in
/-- The difference map is an idempotent after scaling by its positive multiplier. -/
theorem complement_map_square {A : Variety} (S : Subvariety A)
    (N : ℕ) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom) :
    (complementMap S N r).hom ≫ (complementMap S N r).hom =
      (complementMap S N r).hom ^ (N : ℤ) := by
  let e := complementMap S N r
  change e.hom ≫ ((multiplication A N).hom / (r.hom ≫ S.inclusion.hom)) = e.hom ^ (N : ℤ)
  rw [GrpObj.comp_div, multiplication_nat_hom, GrpObj.comp_zpow, Category.comp_id,
    ← Category.assoc, complement_map_comp_retraction S N r hr, MonObj.one_comp, div_one]

set_option maxRecDepth 2000 in
/-- The difference map vanishes on the original subvariety. -/
theorem subvariety_comp_complement_map {A : Variety} (S : Subvariety A)
    (N : ℕ) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom) :
    S.inclusion.hom ≫ (complementMap S N r).hom = (1 : S.B.X ⟶ A.X) := by
  change S.inclusion.hom ≫ ((multiplication A N).hom / (r.hom ≫ S.inclusion.hom)) = 1
  rw [GrpObj.comp_div, multiplication_nat_hom, GrpObj.comp_zpow, Category.comp_id,
    ← Category.assoc, hr, multiplication_nat_hom, GrpObj.zpow_comp, Category.id_comp]
  exact div_self' (S.inclusion.hom ^ (N : ℤ))

end HodgeLean.Foundations.AbelianQuotient
