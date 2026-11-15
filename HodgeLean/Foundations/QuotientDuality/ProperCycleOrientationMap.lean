import HodgeLean.Foundations.QuotientDuality.ProperCycleChainHomology
import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.MapOfLocalStalks

/-! # The orientation sheaf map specified by a global rational class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Opposite
namespace HodgeLean.Foundations.QuotientDuality

lemma properCycle_local_orientation_restrict (X : TopCat.{0}) (N : ℕ)
    (c : Homology ℚ X N) (U : Opens X) (x : X) (hx : x ∈ U) :
    relativeHomologyMap ℚ N (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))
      ((relativeHomologyProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ) N).hom c) =
      localOrientation X N c x := by
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f N)
    (properCycle_relative_projection_restrict X (Set.singleton_subset_iff.mpr hx))
  rw [HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh c

/-- Scalar multiples of the specified global class in the actual homology-sheaf stalk.
Source: Hatcher, Algebraic Topology, section 3.3; HodgeConjecture 2ead713,
Other/AlgebraicGeometry/ComplexPoint/OrientationHomologySheaf.lean.
HC no distance; AV milestone no distance. -/
def properCycle_global_orientation_stalk_map (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N) (x : X) :
    AddCommGrpCat.of ℚ ⟶ (singularChainHomologySheaf ℚ X N).presheaf.stalk x :=
  AddCommGrpCat.ofHom (orientationLine X N c x).toAddMonoidHom ≫
    (singularChainHomologySheafStalkIso ℚ X x N).inv

lemma properCycle_global_orientation_stalk_map_isIso (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x)) (x : X) :
    IsIso (properCycle_global_orientation_stalk_map X N c x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ X x N).inv).mp inferInstance).comp (hlocal x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma properCycle_global_orientation_locally_representable (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N) :
    ∀ (q : ℚ) (x : X), ∃ (U : Opens X) (_ : x ∈ U)
      (s : (singularChainHomologySheaf ℚ X N).presheaf.obj (op U)),
      ∀ (y : X) (hy : y ∈ U),
        (singularChainHomologySheaf ℚ X N).presheaf.germ U y hy s =
          properCycle_global_orientation_stalk_map X N c y q := by
  intro q x
  let U : Opens X := ⊤
  let cU := (relativeHomologyProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ) N).hom c
  refine ⟨U, trivial, relativeHomologyToHomologySheafSection ℚ X U N (q • cU), ?_⟩
  intro y hy
  apply ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ X y N).hom).mp inferInstance).injective
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X U y hy N) (q • cU)
  simp only [ConcreteCategory.comp_apply] at hgerm
  erw [hgerm]
  change relativeHomologyMap ℚ N (supportInclusionPairMap X _) (q • cU) =
    (singularChainHomologySheafStalkIso ℚ X y N).hom
      ((singularChainHomologySheafStalkIso ℚ X y N).inv (q • localOrientation X N c y))
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change relativeHomologyMap ℚ N (supportInclusionPairMap X _) (q • cU) =
    q • localOrientation X N c y
  rw [map_smul]
  exact congrArg (q • ·) (properCycle_local_orientation_restrict X N c U y hy)

/-- Gluing local restrictions of the global class constructs the orientation sheaf map.
Source: Hatcher, Algebraic Topology, section 3.3; HodgeConjecture 2ead713,
Other/AlgebraicGeometry/ComplexPoint/OrientationHomologySheaf.lean.
HC no distance; AV milestone no distance. -/
def properCycle_global_orientation_sheaf_map (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N) :
    TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) ⟶ singularChainHomologySheaf ℚ X N :=
  TopCat.Sheaf.constantSheafMapOfLocallyRepresentable _ (AddCommGrpCat.of ℚ)
    (properCycle_global_orientation_stalk_map X N c)
    (properCycle_global_orientation_locally_representable X N c)

lemma properCycle_global_orientation_sheaf_map_isIso (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x)) :
    IsIso (properCycle_global_orientation_sheaf_map X N c) := by
  unfold properCycle_global_orientation_sheaf_map
  exact TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_isIso
    (singularChainHomologySheaf ℚ X N) (AddCommGrpCat.of ℚ)
    (properCycle_global_orientation_stalk_map X N c)
    (properCycle_global_orientation_locally_representable X N c)
    (properCycle_global_orientation_stalk_map_isIso X N c hlocal)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma properCycle_global_orientation_sheaf_map_stalk (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N) (x : X) :
    (TopCat.Sheaf.constantSheafStalkIso (X := X) (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (properCycle_global_orientation_sheaf_map X N c).hom ≫
      (singularChainHomologySheafStalkIso ℚ X x N).hom =
      AddCommGrpCat.ofHom (orientationLine X N c x).toAddMonoidHom := by
  unfold properCycle_global_orientation_sheaf_map
  rw [← Category.assoc]
  erw [TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_stalk]
  unfold properCycle_global_orientation_stalk_map
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma properCycle_global_orientation_one (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N) (x : X) :
    ((TopCat.Sheaf.constantSheafStalkIso (X := X) (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (properCycle_global_orientation_sheaf_map X N c).hom ≫
      (singularChainHomologySheafStalkIso ℚ X x N).hom) 1 = localOrientation X N c x := by
  rw [properCycle_global_orientation_sheaf_map_stalk]
  change (1 : ℚ) • localOrientation X N c x = localOrientation X N c x
  exact one_smul ℚ _

end HodgeLean.Foundations.QuotientDuality
