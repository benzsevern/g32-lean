module

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.Cochain
public import Mathlib.Topology.Sheaves.Functors

@[expose] public section
noncomputable section
open CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

/-- The maps from inverse images of open sets to those open sets form a natural family. -/
def openPreimageToTarget {A B : TopCat} (q : A ⟶ B) :
    Opens.map q ⋙ Opens.toTopCat A ⟶ Opens.toTopCat B where
  app U := TopCat.ofHom ⟨(U : Set B).restrictPreimage q, q.hom.continuous.restrictPreimage⟩
  naturality {U V} i := by
    ext x
    rfl

/-- Singular chains on inverse images map naturally to chains on the target opens. -/
def singularOpenChainMap (R : Type) [CommRing R] {A B : TopCat} (q : A ⟶ B) :
    Opens.map q ⋙ AlgebraicTopology.Singular.openSingularChainComplexFunctor R A ⟶
      AlgebraicTopology.Singular.openSingularChainComplexFunctor R B := by
  unfold AlgebraicTopology.Singular.openSingularChainComplexFunctor
  exact Functor.whiskerRight (openPreimageToTarget q)
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R))

/-- Actual singular cochain pullbacks form a map of presheaves on the target. -/
def singularOpenCochainMap (R : Type) [CommRing R] {A B : TopCat} (q : A ⟶ B) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainPresheaf R B n ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat q).obj
        (AlgebraicTopology.Singular.singularCochainPresheaf R A n) where
  app U := AddCommGrpCat.ofHom
    ((((singularOpenChainMap R q).app U.unop).f n).hom.dualMap.toAddMonoidHom)
  naturality {U V} i := by
    ext φ
    change AlgebraicTopology.Singular.OpenCochains R B U n at φ
    apply LinearMap.ext
    intro c
    have h := congrArg (fun f => φ ((f.f n).hom c))
      ((singularOpenChainMap R q).naturality i.unop)
    exact h.symm

/-- The presheaf pullback commutes with the actual singular coboundary. -/
theorem singularOpenCochainMap_coboundary (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainCoboundary R B n ≫
        singularOpenCochainMap R q (n + 1) =
      singularOpenCochainMap R q n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat q).map
          (AlgebraicTopology.Singular.singularCochainCoboundary R A n) := by
  apply NatTrans.ext
  funext U
  ext φ
  change AlgebraicTopology.Singular.OpenCochains R B U n at φ
  apply LinearMap.ext
  intro c
  have h := congrArg (fun f => φ (f.hom c))
    (((singularOpenChainMap R q).app U.unop).comm (n + 1) n)
  exact h

/-- Sheafification extends the actual singular cochain pullback. -/
def singularCochainSheafPullback (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainSheaf R B n ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat q).obj
        (AlgebraicTopology.Singular.singularCochainSheaf R A n) :=
  ⟨sheafifyLift (Opens.grothendieckTopology B)
    (singularOpenCochainMap R q n ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat q).map
        (toSheafify (Opens.grothendieckTopology A)
          (AlgebraicTopology.Singular.singularCochainPresheaf R A n)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj
      (AlgebraicTopology.Singular.singularCochainSheaf R A n)).property⟩

/-- The sheaf pullback retains the actual presheaf pullback under sheafification. -/
@[reassoc]
theorem singularCochainSheafPullback_unit (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) (n : ℕ) :
    toSheafify (Opens.grothendieckTopology B)
        (AlgebraicTopology.Singular.singularCochainPresheaf R B n) ≫
      (singularCochainSheafPullback R q n).hom =
    singularOpenCochainMap R q n ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat q).map
        (toSheafify (Opens.grothendieckTopology A)
          (AlgebraicTopology.Singular.singularCochainPresheaf R A n)) :=
  toSheafify_sheafifyLift _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified singular pullback commutes with coboundary. -/
theorem singularCochainSheafPullback_coboundary (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainSheafCoboundary R B n ≫
        singularCochainSheafPullback R q (n + 1) =
      singularCochainSheafPullback R q n ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat q).map
          (AlgebraicTopology.Singular.singularCochainSheafCoboundary R A n) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology B) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat q).obj
      (AlgebraicTopology.Singular.singularCochainSheaf R A (n + 1))).property
  change toSheafify _ _ ≫
      (sheafifyMap (Opens.grothendieckTopology B)
        (AlgebraicTopology.Singular.singularCochainCoboundary R B n) ≫
          (singularCochainSheafPullback R q (n + 1)).hom) =
    toSheafify _ _ ≫ ((singularCochainSheafPullback R q n).hom ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat q).map
        (sheafifyMap (Opens.grothendieckTopology A)
          (AlgebraicTopology.Singular.singularCochainCoboundary R A n)))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    singularCochainSheafPullback_unit, ← Category.assoc,
    singularOpenCochainMap_coboundary, Category.assoc,
    ← (TopCat.Presheaf.pushforward AddCommGrpCat q).map_comp,
    toSheafify_naturality, (TopCat.Presheaf.pushforward AddCommGrpCat q).map_comp,
    ← Category.assoc, ← singularCochainSheafPullback_unit, Category.assoc]

/-- The actual sheafified singular pullbacks assemble into a morphism of complexes. -/
def singularCochainSheafComplexPullback (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) :
    AlgebraicTopology.Singular.singularCochainSheafComplex R B ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (AlgebraicTopology.Singular.singularCochainSheafComplex R A) where
  f n := singularCochainSheafPullback R q n
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst j
    change singularCochainSheafPullback R q i ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat q).map
          ((AlgebraicTopology.Singular.singularCochainSheafComplex R A).d i (i + 1)) =
      (AlgebraicTopology.Singular.singularCochainSheafComplex R B).d i (i + 1) ≫
        singularCochainSheafPullback R q (i + 1)
    simp only [AlgebraicTopology.Singular.singularCochainSheafComplex_d]
    exact (singularCochainSheafPullback_coboundary R q i).symm

/-- The actual maps on open singular chains preserve zero-chain augmentation. -/
theorem singularOpenChainMap_zeroAugmentation (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) (U : Opens B) :
    ((singularOpenChainMap R q).app U).f 0 ≫
        AlgebraicTopology.Singular.openZeroAugmentation R B (op U) =
      AlgebraicTopology.Singular.openZeroAugmentation R A (op ((Opens.map q).obj U)) :=
  AlgebraicTopology.Singular.simplicialZeroAugmentation_naturality R
    (TopCat.toSSet.map ((openPreimageToTarget q).app U))

/-- Actual presheaf pullback preserves the constant singular zero-cochains. -/
theorem singularOpenCochainMap_constants (R : Type) [CommRing R]
    {A B : TopCat} (q : A ⟶ B) :
    AlgebraicTopology.Singular.constantsToSingularCochainZero R B ≫
        singularOpenCochainMap R q 0 =
      (TopCat.Presheaf.pushforward AddCommGrpCat q).map
        (AlgebraicTopology.Singular.constantsToSingularCochainZero R A) := by
  apply NatTrans.ext
  funext U
  ext r
  change R at r
  apply LinearMap.ext
  intro c
  change r * (AlgebraicTopology.Singular.openZeroAugmentation R B U).hom
      ((((singularOpenChainMap R q).app U.unop).f 0).hom c) =
    r * (AlgebraicTopology.Singular.openZeroAugmentation R A
      (op ((Opens.map q).obj U.unop))).hom c
  exact congrArg (r * ·) (congrArg (fun f => f.hom c)
    (singularOpenChainMap_zeroAugmentation R q U.unop))

end HodgeLean.Foundations.Program
