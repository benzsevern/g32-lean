import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainOrientation
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.MapOfLocalStalks
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified global orientation gives scalar maps into the actual chain-homology stalks. -/
def retainedOrientationStalkMap (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (x : X) :
    AddCommGrpCat.of ℚ ⟶ (singularChainHomologySheaf ℚ X n).presheaf.stalk x :=
  AddCommGrpCat.ofHom (orientationLine X n c x).toAddMonoidHom ≫
    (singularChainHomologySheafStalkIso ℚ X x n).inv

/-- Local orientation bijectivity makes the specified stalk map an isomorphism. -/
theorem retained_orientation_stalk_map_isIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (x : X)
    (ho : Function.Bijective (orientationLine X n c x)) :
    IsIso (retainedOrientationStalkMap X n c x) := by
  letI : IsIso (AddCommGrpCat.ofHom (orientationLine X n c x).toAddMonoidHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ho
  unfold retainedOrientationStalkMap
  infer_instance

/-- Projecting a global class to a larger support and then restricting gives its original local projection. -/
theorem retained_relative_projection_support_inclusion (X : TopCat.{0})
    {S T : Set X} (h : S ⊆ T) (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (supportInclusionPairMap X h)
      ((relativeHomologyProjection ℚ (TopPair.ofSubset Tᶜ) n).hom c) =
      (relativeHomologyProjection ℚ (TopPair.ofSubset Sᶜ) n).hom c := by
  have hc := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (relativeChainProjection_supportInclusion ℚ X h)
  rw [HomologicalComplex.homologyMap_comp] at hc
  exact ConcreteCategory.congr_hom hc c

/-- The actual global class represents every scalar orientation stalk map on the whole space. -/
theorem retained_orientation_stalk_map_locallyRepresentable
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (c : Homology ℚ X n) :
    ∀ (q : ℚ) (x : X), ∃ (U : Opens X) (_ : x ∈ U)
      (s : (singularChainHomologySheaf ℚ X n).presheaf.obj (op U)),
      ∀ (y : X) (hy : y ∈ U),
        (singularChainHomologySheaf ℚ X n).presheaf.germ U y hy s =
          retainedOrientationStalkMap X n c y q := by
  intro q x
  let U : Opens X := ⊤
  let cU := (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n).hom c
  refine ⟨U, Set.mem_univ _, relativeHomologyToHomologySheafSection ℚ X U n (q • cU), ?_⟩
  intro y hy
  apply ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ X y n).hom).mp inferInstance).injective
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X U y hy n) (q • cU)
  simp only [ConcreteCategory.comp_apply] at hgerm
  erw [hgerm]
  change relativeHomologyMap ℚ n (supportInclusionPairMap X _) (q • cU) =
    (singularChainHomologySheafStalkIso ℚ X y n).hom
      ((singularChainHomologySheafStalkIso ℚ X y n).inv (q • localOrientation X n c y))
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change relativeHomologyMap ℚ n (supportInclusionPairMap X _) (q • cU) =
    q • localOrientation X n c y
  rw [map_smul]
  exact congrArg (q • ·) (retained_relative_projection_support_inclusion X
    (Set.singleton_subset_iff.mpr hy) n c)

/-- The chain-homology sheaf orientation assembled from the specified global class. -/
def retainedOrientationHomologySheafIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (ho : ∀ x, Function.Bijective (orientationLine X n c x)) :
    𝓒(X; ℚ) ≅ singularChainHomologySheaf ℚ X n := by
  let f := TopCat.Sheaf.constantSheafMapOfLocallyRepresentable
    (singularChainHomologySheaf ℚ X n) (AddCommGrpCat.of ℚ)
    (retainedOrientationStalkMap X n c)
    (retained_orientation_stalk_map_locallyRepresentable X n c)
  letI : IsIso f := TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_isIso
    (singularChainHomologySheaf ℚ X n) (AddCommGrpCat.of ℚ)
    (retainedOrientationStalkMap X n c)
    (retained_orientation_stalk_map_locallyRepresentable X n c)
    (fun x => retained_orientation_stalk_map_isIso X n c x (ho x))
  exact asIso f

/-- On stalks the assembled orientation is exactly scalar multiplication by the specified local class. -/
theorem retained_orientation_homology_sheaf_iso_stalk
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x)) (x : X) :
    (TopCat.Sheaf.constantSheafStalkIso (X := X) (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (retainedOrientationHomologySheafIso X n c ho).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ X x n).hom =
      AddCommGrpCat.ofHom (orientationLine X n c x).toAddMonoidHom := by
  unfold retainedOrientationHomologySheafIso
  rw [← Category.assoc]
  erw [TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_stalk]
  unfold retainedOrientationStalkMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HodgeLean.Foundations.QuotientDuality
