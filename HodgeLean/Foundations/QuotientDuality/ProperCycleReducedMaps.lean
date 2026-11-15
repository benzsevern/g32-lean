import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification

/-! # Actual reduced remainder and smooth-open morphisms over the complex base -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual reduced remainder inclusion, retaining its complex structure morphism.
Source: Hartshorne, Algebraic Geometry, II.5, reduced closed subschemes.
HC no distance; AV milestone no distance. -/
def properCycle_reduced_closed_map (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] (T : Closeds X.left) :
    Over.mk (reducedClosedStructureMap X.hom T) ⟶ X :=
  Over.homMk (reducedClosedSubschemeι T) rfl

instance properCycle_reduced_closed_map_isClosedImmersion (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] (T : Closeds X.left) :
    IsClosedImmersion (properCycle_reduced_closed_map X T).left := by
  change IsClosedImmersion (reducedClosedSubschemeι T)
  infer_instance

/-- The actual smooth-open inclusion into its reduced remainder.
Source: EGA IV, 17.3.8, openness of the smooth locus.
HC no distance; AV milestone no distance. -/
def properCycle_reduced_smooth_open_map (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] (T : Closeds X.left) :
    Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom) ⟶
      Over.mk (reducedClosedStructureMap X.hom T) :=
  Over.homMk (reducedClosedStructureMap X.hom T).smoothLocus.ι
    (by
      change (reducedClosedStructureMap X.hom T).smoothLocus.ι ≫
        (reducedClosedSubschemeι T ≫ X.hom) =
          ((reducedClosedStructureMap X.hom T).smoothLocus.ι ≫ reducedClosedSubschemeι T) ≫ X.hom
      exact (Category.assoc _ _ _).symm)

instance properCycle_reduced_smooth_open_map_isOpenImmersion (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] (T : Closeds X.left) :
    IsOpenImmersion (properCycle_reduced_smooth_open_map X T).left := by
  change IsOpenImmersion (reducedClosedStructureMap X.hom T).smoothLocus.ι
  infer_instance

end HodgeLean.Foundations.QuotientDuality
