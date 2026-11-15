import HodgeLean.Foundations.BundleResolution.ChernRelativeCapToBaseHelpers

/-! # Actual projected cap bijectivity from integer-extended global cap

The extension homology isomorphisms identify the actual projected cap
with the homology map of the checked global chain comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeCapToBase_bijective_of_global_quasiIso (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (k n : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    [QuasiIso (i1_globalEvenCapExtendedMap X Y f Z k φ)] :
    Function.Bijective (i1_relativeCapToBase X Y f Z (2 * k) n
      (i1_relativeCocycleClass (TopPair.ofSubset (X := X) Z) (2 * k) φ)) := by
  let P := TopPair.ofSubset (X := X) Z
  let K := (relativeChainFunctor ℚ).obj P
  let L := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y
  let eK := K.extendHomologyIso (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
    (show (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f (2 * k + n) = -(n : ℤ) by
      simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  let eL := L.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
    (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
      simp only [ComplexShape.embeddingUpIntLE_f]; omega)
  let m := HomologicalComplex.homologyMap (i1_globalEvenCapExtendedMap X Y f Z k φ) (-(n : ℤ))
  let t := ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P (2 * k) n φ.val φ.property) ≫
    HomologicalComplex.homologyMap (singularChainComplexMap ℚ f) n
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  have hm : eK.inv ≫ m ≫ eL.hom = t := i1_globalEvenCapExtendedMap_homology X Y f Z k n φ
  haveI : IsIso t := by
    have ht : IsIso (eK.inv ≫ m ≫ eL.hom) := inferInstance
    exact hm ▸ ht
  dsimp only [i1_relativeCapToBase]
  rw [i1_relativeCapCohomologyLinear_class]
  change Function.Bijective t
  exact ConcreteCategory.bijective_of_isIso t

end HodgeLean.Foundations.BundleResolution
