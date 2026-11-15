import HodgeLean.Foundations.QuotientDuality.ProperCycleDimension

/-! # Dimension bounds for images of actual scheme points -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The dimension of the closure of an actual scheme point cannot increase under a morphism of finite-type complex schemes.
Source: Hartshorne, Algebraic Geometry, exercise II.3.20; transcendence degree in the actual residue-field tower.
HC no distance; AV milestone no distance. -/
lemma properCycle_height_image_le {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (x : X.left) : Order.height (f.left x) ≤ Order.height x := by
  letI : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  letI : Algebra ℂ (Y.left.residueField (f.left x)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ Y.hom.appTop ≫
      Y.left.Γevaluation (f.left x)).hom.toAlgebra
  letI := (f.left.residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower ℂ (Y.left.residueField (f.left x)) (X.left.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap x (Y.left.Γevaluation (f.left x) (Y.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation x ((Y.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  obtain ⟨_, n, hn, htr⟩ := a1d_height_eq_trdeg x
  obtain ⟨_, m, hm, htr'⟩ := a1d_height_eq_trdeg (f.left x)
  have hadd := trdeg_add_eq ℂ (Y.left.residueField (f.left x)) (A := X.left.residueField x)
  rw [htr, htr'] at hadd
  have hmn : (m : Cardinal) ≤ (n : Cardinal) := le_self_add.trans hadd.le
  rw [hn, hm]
  exact_mod_cast hmn

end HodgeLean.Foundations.QuotientDuality
