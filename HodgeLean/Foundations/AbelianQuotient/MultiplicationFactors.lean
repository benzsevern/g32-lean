import HodgeLean.Foundations.AbelianQuotient.PointMultiplication
import HodgeLean.Foundations.AbelianQuotient.ComplementMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- An algebraic factor of positive multiplication is onto on complex points. -/
theorem surjective_of_multiplication_factor {A B : Variety} (q : Hom A B) (i : Hom B A)
    (N : ℕ) (hN : 0 < N) (hiq : i.hom ≫ q.hom = (multiplication B N).hom) :
    Function.Surjective (Point.map q.hom) := by
  intro b
  obtain ⟨c, hc⟩ := surjective_pow_points B N hN b
  refine ⟨Point.map i.hom c, ?_⟩
  rw [← Point.map_comp_apply, hiq, multiplication_nat_hom]
  change c ≫ ((𝟙 B.X) ^ (N : ℤ)) = b
  rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast]
  exact hc

set_option maxRecDepth 2000 in
/-- A multiplication factor of the difference map annihilates the original subvariety. -/
theorem subvariety_comp_difference_factor {A B : Variety} (S : Subvariety A)
    (N : ℕ) (hN : 0 < N) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom)
    (q : Hom A B) (i : Hom B A)
    (hqi : q.hom ≫ i.hom = (complementMap S N r).hom)
    (hiq : i.hom ≫ q.hom = (multiplication B N).hom) :
    S.inclusion.hom ≫ q.hom = (1 : S.B.X ⟶ B.X) := by
  let u : Hom S.B B := ⟨S.inclusion.hom ≫ q.hom, inferInstance⟩
  have hSi : u.hom ≫ i.hom = (1 : S.B.X ⟶ A.X) := by
    change (S.inclusion.hom ≫ q.hom) ≫ i.hom = 1
    rw [Category.assoc, hqi, subvariety_comp_complement_map S N r hr]
  have hp := congrArg (fun k : S.B.X ⟶ A.X => k ≫ q.hom) hSi
  rw [Category.assoc, hiq, multiplication_nat_hom,
    GrpObj.comp_zpow, Category.comp_id, MonObj.one_comp] at hp
  exact hom_eq_one_of_pow_eq_one u N hN hp

end HodgeLean.Foundations.AbelianQuotient
