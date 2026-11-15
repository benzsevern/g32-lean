import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf

/-! Normalization of actual singular classes in the orientation homology sheaf.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A locally normalized relative class gives the orientation section with coefficient one.
Source: Bredon, Sheaf Theory, second edition, V.9, the orientation sheaf and its generators.
HC no distance; AV milestone no distance.
-/
theorem relative_orientation_section_one (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (U : Opens X)
    (w : RelativeHomology ℚ (TopPair.ofSubset (U : Set X)ᶜ) n)
    (hw : ∀ (x : X) (hx : x ∈ U), relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w = o.generator x) :
    relativeHomologyToHomologySheafSection ℚ X U n w =
      (localOrientationHomologySheafIso X n o).hom.hom.app (op U)
        (constSection (AddCommGrpCat.of ℚ) U 1) := by
  apply TopCat.Presheaf.section_ext (singularChainHomologySheaf ℚ X n) U
  intro x hx
  apply (ConcreteCategory.bijective_of_isIso (singularChainHomologySheafStalkIso ℚ X x n).hom).1
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X U x hx n) w
  simp only [ConcreteCategory.comp_apply] at hgerm
  calc
    _ = relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w := hgerm
    _ = o.generator x := hw x hx
    _ = _ := by
      erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        (localOrientationHomologySheafIso X n o).hom.hom]
      erw [germ_constSection_top, germ_constSection_eq_constantSheafStalkIso]
      exact (localOrientationHomologySheafIso_stalk_one X n o x).symm

#print axioms relative_orientation_section_one
/-- A normalized absolute class maps to the coefficient-one global orientation section.
Source: Bredon, Sheaf Theory, second edition, V.9, normalization of the orientation section.
HC no distance; AV milestone no distance.
-/
theorem absolute_orientation_section_one (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : localization X n c = o.generator) :
    relativeHomologyToHomologySheafSection ℚ X ⊤ n
      ((relativeHomologyProjection ℚ
        (TopPair.ofSubset (((⊤ : Opens X) : Set X)ᶜ)) n).hom c) =
      (localOrientationHomologySheafIso X n o).hom.hom.app (op ⊤)
        (constSection (AddCommGrpCat.of ℚ) ⊤ 1) := by
  apply relative_orientation_section_one
  intro x hx
  have hn := relativeHomologyProjection_map n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top x))) c
  have hi : (supportInclusionPairMap X
      (Set.singleton_subset_iff.mpr (Opens.mem_top x))).hom.right = 𝟙 X := rfl
  rw [hi] at hn
  erw [homologyMap_id] at hn
  exact hn.trans (congrFun hc x)

#print axioms absolute_orientation_section_one
end HodgeLean.Foundations.RationalHomologyManifold
