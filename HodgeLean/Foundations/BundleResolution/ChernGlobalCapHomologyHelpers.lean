import HodgeLean.Foundations.BundleResolution.ChernGlobalDomainCapChainHelpers
import HodgeLean.Foundations.BundleResolution.ChernEvenCapHomologyHelpers

/-! # Actual global cap homology after the continuous base projection

The integer extension homology isomorphisms retain actual relative cap
and the actual map on absolute homology induced by the projection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_globalEvenCapExtendedMap_homology (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X)
    (k n : ℕ) (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    let K := (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)
    let L := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y
    (K.extendHomologyIso (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
      (show (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f (2 * k + n) = -(n : ℤ) by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv ≫
      homologyMap (i1_globalEvenCapExtendedMap X Y f Z k φ) (-(n : ℤ)) ≫
      (L.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom =
      ShortComplex.homologyMap
        (relativeCapShortComplexHom ℚ (TopPair.ofSubset (X := X) Z) (2 * k) n φ.val φ.property) ≫
        homologyMap (singularChainComplexMap ℚ f) n := by
  let P := TopPair.ofSubset (X := X) Z
  let K := (relativeChainFunctor ℚ).obj P
  let M := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj X
  let L := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y
  let eK := K.extendHomologyIso (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
    (show (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f (2 * k + n) = -(n : ℤ) by
      simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  let eM := M.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
    (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
      simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  let eL := L.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
    (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
      simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  let c := i1_evenRelativeCapExtendedChainMap P k φ.val φ.property
  have hn : homologyMap (HomologicalComplex.extendMap (singularChainComplexMap ℚ f)
        (ComplexShape.embeddingUpIntLE 0)) (-(n : ℤ)) ≫ eL.hom =
      eM.hom ≫ homologyMap (singularChainComplexMap ℚ f) n :=
    extendHomologyIso_hom_naturality (singularChainComplexMap ℚ f) (ComplexShape.embeddingUpIntLE 0)
      (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  have hc : eK.inv ≫ homologyMap c (-(n : ℤ)) ≫ eM.hom =
      ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P (2 * k) n φ.val φ.property) :=
    i1_evenRelativeCapExtendedChainMap_homology P k n φ.val φ.property
  dsimp only
  change eK.inv ≫ homologyMap (c ≫ HomologicalComplex.extendMap (singularChainComplexMap ℚ f)
      (ComplexShape.embeddingUpIntLE 0)) (-(n : ℤ)) ≫ eL.hom = _
  erw [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [hn]
  have hh := congrArg (fun q => q ≫ homologyMap (singularChainComplexMap ℚ f) n) hc
  simpa only [HomologicalComplex.homology, Category.assoc] using hh

end HodgeLean.Foundations.BundleResolution
