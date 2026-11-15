import HodgeLean.Foundations.QuotientDuality.ProperCycleOrientationMap
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainOrientation

/-! # Derived orientation determined by an actual global rational class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_orientation_derived_category (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _

/-- Concentration and the constructed fundamental-class map give the actual derived orientation.
Source: Bredon, Sheaf Theory, second edition, V.9; HodgeConjecture 2ead713,
Other/AlgebraicTopology/Singular/Sheaf/ChainOrientation.lean.
HC no distance; AV milestone no distance. -/
def properCycle_global_derived_orientation (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ≅
      (DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) := by
  letI hmap : IsIso (properCycle_global_orientation_sheaf_map X N c) :=
    properCycle_global_orientation_sheaf_map_isIso X N c hlocal
  exact DerivedCategory.concentratedOrientationIso (singularChainSheafCochainComplex ℚ X)
    (-(N : ℤ)) (properCycle_chain_cohomology_concentrated X N hvan)
    (singularChainSheafCochainHomologyIso ℚ X N ≪≫
      (asIso (properCycle_global_orientation_sheaf_map X N c)).symm)

lemma properCycle_global_derived_orientation_homology (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    (DerivedCategory.homologyFunctor _ (-(N : ℤ))).map
        (properCycle_global_derived_orientation X N c hlocal hvan).hom ≫
      (DerivedCategory.homologyFunctorFactors _ (-(N : ℤ))).hom.app
        ((single _ (ComplexShape.up ℤ) (-(N : ℤ))).obj
          (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))) ≫
      (singleObjHomologySelfIso (ComplexShape.up ℤ) (-(N : ℤ))
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))).hom ≫
      properCycle_global_orientation_sheaf_map X N c =
      (DerivedCategory.homologyFunctorFactors _ (-(N : ℤ))).hom.app
        (singularChainSheafCochainComplex ℚ X) ≫
      (singularChainSheafCochainHomologyIso ℚ X N).hom := by
  letI hmap : IsIso (properCycle_global_orientation_sheaf_map X N c) :=
    properCycle_global_orientation_sheaf_map_isIso X N c hlocal
  dsimp only [properCycle_global_derived_orientation]
  rw [DerivedCategory.concentratedOrientationIso_homology_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom]
  have hp : (asIso (properCycle_global_orientation_sheaf_map X N c)).inv ≫
      properCycle_global_orientation_sheaf_map X N c = 𝟙 _ :=
    (asIso (properCycle_global_orientation_sheaf_map X N c)).inv_hom_id
  let B := (singularChainSheafCochainHomologyIso ℚ X N).hom
  have hB : (B ≫ (asIso (properCycle_global_orientation_sheaf_map X N c)).inv) ≫
      properCycle_global_orientation_sheaf_map X N c = B :=
    (Category.assoc B _ _).trans
      ((congrArg (fun f => B ≫ f) hp).trans (Category.comp_id B))
  exact congrArg (fun f =>
    (DerivedCategory.homologyFunctorFactors _ (-(N : ℤ))).hom.app
      (singularChainSheafCochainComplex ℚ X) ≫ f) hB

end HodgeLean.Foundations.QuotientDuality
