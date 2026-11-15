import HodgeLean.Foundations.Topology.RationalSheafComparisonDefs

/-! Compatibility of singular sheaf pullback with the constant augmentation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.Foundations.Program

namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem pullbackConstantsIso_hom_adjunct {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A : AddCommGrpCat.{0}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv _ _
      (pullbackConstantsIso f A).hom = TopCat.Sheaf.constantRestriction f A := by
  let aY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat isTerminalTop
  let aX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop
  apply (aY.homEquiv A _).injective
  have h := (aY.comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)).homEquiv_leftAdjointUniq_hom_app aX A
  rw [Adjunction.comp_homEquiv] at h
  change aY.homEquiv A _
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv _ _
      (((aY.comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)).leftAdjointUniq aX).hom.app A)) = _
  calc
    _ = aX.unit.app A := h
    _ = _ := by
      rw [Adjunction.homEquiv_unit]
      change _ = (toSheafify (Opens.grothendieckTopology Y)
        (TopCat.Presheaf.const Y A)).app (op ⊤) ≫
          (TopCat.Sheaf.constantRestriction f A).hom.app (op ⊤)
      exact (NatTrans.congr_app (TopCat.Sheaf.toSheafify_constantRestriction f A) (op ⊤)).symm

/-- Source: Bredon, Sheaf Theory, second edition, III.1. -/
theorem singularPullback_constants {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantsToSingularCochainZeroSheaf ℚ Y ≫ singularCochainSheafPullback ℚ f 0 =
      TopCat.Sheaf.constantRestriction f (AddCommGrpCat.of ℚ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map
          (constantsToSingularCochainZeroSheaf ℚ X) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology Y) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj
      (singularCochainSheaf ℚ X 0)).property
  change toSheafify _ _ ≫
      (sheafifyMap (Opens.grothendieckTopology Y)
        (constantsToSingularCochainZero ℚ Y) ≫
          (singularCochainSheafPullback ℚ f 0).hom) =
    toSheafify _ _ ≫ ((TopCat.Sheaf.constantRestriction f (AddCommGrpCat.of ℚ)).hom ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat f).map
        (sheafifyMap (Opens.grothendieckTopology X)
          (constantsToSingularCochainZero ℚ X)))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    singularCochainSheafPullback_unit, ← Category.assoc,
    singularOpenCochainMap_constants,
    ← (TopCat.Presheaf.pushforward AddCommGrpCat f).map_comp,
    toSheafify_naturality]
  rw [← Category.assoc, TopCat.Sheaf.toSheafify_constantRestriction]
  rfl

/-- Source: Bredon, Sheaf Theory, second edition, III.1. -/
theorem singularPullback_augmentation {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantsToSingularCochainSheafComplex ℚ Y ≫ singularCochainSheafComplexPullback ℚ f =
      (CochainComplex.single₀ _).map
        (TopCat.Sheaf.constantRestriction f (AddCommGrpCat.of ℚ)) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pushforward AddCommGrpCat f) (.up ℕ) 0).inv.app (constants X) ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).map
        (constantsToSingularCochainSheafComplex ℚ X) := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  change constantsToSingularCochainZeroSheaf ℚ Y ≫ singularCochainSheafPullback ℚ f 0 = _
  exact singularPullback_constants f

end HodgeLean.Topology.RationalSheafComparison
