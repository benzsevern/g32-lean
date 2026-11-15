import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.ShortComplex.Abelian

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace HodgeLean.Adapters

universe u

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: homology transports a canonical mapped-arrow
comparison to the ordinary homology map of the corresponding cone comparison. -/
theorem a3sv_mappingConeMappedArrow_homology_naturality
    {B : Type u} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) (n : ℤ) :
    let X := HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)
    let H := HomotopyCategory.homologyFunctor
      (ModuleCat.{u} B) (ComplexShape.up ℤ) 0
    (H.shift n).map (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso f).hom) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
          (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone (F.map f)) =
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
          (ComplexShape.up ℤ) n).hom.app
            ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} B)).obj
              ((F.mapComposableArrows 1).obj (mk₁ f))) ≫
        HomologicalComplex.homologyMap
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} B)).map
            (F.mapComposableArrowsObjMk₁Iso f).hom) n := by
  dsimp only
  exact (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
    (ComplexShape.up ℤ) n).hom.naturality
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).hom)

end HodgeLean.Adapters
