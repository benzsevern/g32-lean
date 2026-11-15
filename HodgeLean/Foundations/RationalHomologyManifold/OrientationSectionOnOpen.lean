import HodgeLean.Foundations.RationalHomologyManifold.OrientationSectionNormalization

/-! Normalized actual absolute classes on arbitrary open supports.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actually normalized absolute class gives the coefficient-one orientation section on every open support.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; naturality of the normalized orientation section.
HC no distance; AV milestone no distance.
-/
theorem absolute_orientation_section_on_open (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : localization X n c = o.generator) (U : Opens X) :
    relativeHomologyToHomologySheafSection ℚ X U n
      ((relativeHomologyProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ) n).hom c) =
      (localOrientationHomologySheafIso X n o).hom.hom.app (op U)
        (constSection (AddCommGrpCat.of ℚ) U 1) := by
  apply relative_orientation_section_one
  intro x hx
  have hn := relativeHomologyProjection_map n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) c
  have hi : (supportInclusionPairMap X
      (Set.singleton_subset_iff.mpr hx)).hom.right = 𝟙 X := rfl
  rw [hi] at hn
  erw [homologyMap_id] at hn
  exact hn.trans (congrFun hc x)

#print axioms absolute_orientation_section_on_open
end HodgeLean.Foundations.RationalHomologyManifold
