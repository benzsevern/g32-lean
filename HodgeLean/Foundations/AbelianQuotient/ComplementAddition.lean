import HodgeLean.Foundations.AbelianQuotient.ComplementMap
import HodgeLean.Foundations.AbelianQuotient.PointMultiplication

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- A multiplication retraction and its difference image give an addition isogeny. -/
theorem addition_isogeny_of_retraction {A : Variety} (S T : Subvariety A)
    (N : ℕ) (hN : 0 < N) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom)
    (p : A.X ⟶ T.B.X) (hp : p ≫ T.inclusion.hom = (complementMap S N r).hom)
    (hTr : T.inclusion.hom ≫ r.hom = (1 : T.B.X ⟶ S.B.X)) :
    ccm2_IsogenyOnPoints (additionMap S T) := by
  let P := S.B.X ⊗ T.B.X
  let pr1 := fst S.B.X T.B.X
  let pr2 := snd S.B.X T.B.X
  have hsum : ∀ z : ComplexPoint P, Point.map (additionMap S T) z =
      Point.map S.inclusion.hom (Point.map pr1 z) *
        Point.map T.inclusion.hom (Point.map pr2 z) := by
    intro z
    change z ≫ ((pr1 ≫ S.inclusion.hom) * (pr2 ≫ T.inclusion.hom)) =
      ((z ≫ pr1) ≫ S.inclusion.hom) * ((z ≫ pr2) ≫ T.inclusion.hom)
    rw [MonObj.comp_mul]
    simp only [Category.assoc]
  have hiR : ∀ x : ComplexPoint S.B.X,
      Point.map r.hom (Point.map S.inclusion.hom x) = x ^ N := by
    intro x
    rw [← Point.map_comp_apply, hr, multiplication_nat_hom]
    change x ≫ ((𝟙 S.B.X) ^ (N : ℤ)) = x ^ N
    rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast]
  have htR : ∀ y : ComplexPoint T.B.X,
      Point.map r.hom (Point.map T.inclusion.hom y) = 1 := by
    intro y
    rw [← Point.map_comp_apply, hTr]
    exact MonObj.comp_one y
  have hR : ∀ z : ComplexPoint P,
      Point.map r.hom (Point.map (additionMap S T) z) = (Point.map pr1 z) ^ N := by
    intro z
    rw [hsum]
    calc
      _ = Point.map r.hom (Point.map S.inclusion.hom (Point.map pr1 z)) *
          Point.map r.hom (Point.map T.inclusion.hom (Point.map pr2 z)) :=
        MonObj.mul_comp _ _ r.hom
      _ = _ := by rw [hiR, htR, mul_one]
  refine ⟨?_, ?_⟩
  · refine Set.Finite.of_injOn (f := Point.map pr1) ?_ ?_
      (abq_finite_pow_kernel S.B.X N hN)
    · intro z hz
      change (Point.map pr1 z) ^ N = 1
      rw [← hR z, hz]
      exact MonObj.one_comp r.hom
    · intro z hz w hw hfst
      have hmul := ((hsum z).symm.trans hz).trans (((hsum w).symm.trans hw).symm)
      rw [hfst] at hmul
      have hy := mul_left_cancel hmul
      haveI : Mono T.inclusion.hom := Over.mono_of_mono_left T.inclusion.hom
      apply hom_ext
      · exact hfst
      · apply (cancel_mono T.inclusion.hom).mp
        exact hy
  · intro a
    obtain ⟨b, hb⟩ := surjective_pow_points A N hN a
    refine ⟨lift (Point.map r.hom b) (Point.map p b), ?_⟩
    rw [hsum]
    change ((lift _ _ ≫ pr1) ≫ S.inclusion.hom) *
      ((lift _ _ ≫ pr2) ≫ T.inclusion.hom) = a
    rw [lift_fst, lift_snd]
    change ((b ≫ r.hom) ≫ S.inclusion.hom) * ((b ≫ p) ≫ T.inclusion.hom) = a
    simp only [Category.assoc]
    rw [hp]
    change (b ≫ r.hom ≫ S.inclusion.hom) *
      (b ≫ ((multiplication A N).hom / (r.hom ≫ S.inclusion.hom))) = a
    rw [GrpObj.comp_div, multiplication_nat_hom, GrpObj.comp_zpow,
      Category.comp_id, zpow_natCast]
    calc
      _ = b ^ N := by rw [mul_comm, div_mul_cancel]
      _ = a := hb

end HodgeLean.Foundations.AbelianQuotient
