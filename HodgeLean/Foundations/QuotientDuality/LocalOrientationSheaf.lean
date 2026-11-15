import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.OrientationConstant
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.MapOfLocalStalks
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainHomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.HomologySection

/-! The orientation section identifies the actual homology sheaf with constants. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite

namespace HodgeLean.Foundations.QuotientDuality

open AlgebraicTopology.Singular

variable (X : TopCat.{0}) (n : ℕ) (o : LocalRationalOrientation X n) [T2Space X]


def localOrientationHomologyStalkMap (x : X) :
    AddCommGrpCat.of ℚ ⟶
      (singularChainHomologySheaf ℚ X n).presheaf.stalk x :=
  AddCommGrpCat.ofHom
    ((LinearMap.toSpanSingleton ℚ _ (o.generator x)).toAddMonoidHom) ≫
      (singularChainHomologySheafStalkIso ℚ X x n).inv


theorem localOrientationHomologyStalkMap_locallyRepresentable :
    ∀ (q : ℚ) (x : X),
      ∃ (U : Opens X) (_ : x ∈ U)
        (s : (singularChainHomologySheaf ℚ X
          n).presheaf.obj (op U)),
        ∀ (y : X) (hy : y ∈ U),
          (singularChainHomologySheaf ℚ X
            n).presheaf.germ U y hy s =
              localOrientationHomologyStalkMap X n o y q := by
  intro q x
  obtain ⟨U, hx, c, hc⟩ := o.coherent x
  refine ⟨U, hx, relativeHomologyToHomologySheafSection ℚ X U n (q • c), ?_⟩
  intro y hy
  apply ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ X
      y n).hom).mp inferInstance).injective
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ
      X U y hy n) (q • c)
  simp only [ConcreteCategory.comp_apply] at hgerm
  erw [hgerm]
  change relativeHomologyMap ℚ n (supportInclusionPairMap _ _) (q • c) =
    (singularChainHomologySheafStalkIso ℚ X
      y n).hom ((singularChainHomologySheafStalkIso ℚ
        X y n).inv
          (q • o.generator y))
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change relativeHomologyMap ℚ n (supportInclusionPairMap _ _) (q • c) =
    q • o.generator y
  rw [map_smul]
  exact congrArg (q • ·) (hc y hy)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in

theorem localOrientationHomologyStalkMap_isIso (x : X) :
    IsIso (localOrientationHomologyStalkMap X n o x) := by
  have hbij := o.generates x
  let : IsIso (AddCommGrpCat.ofHom
      ((LinearMap.toSpanSingleton ℚ _ (o.generator x)).toAddMonoidHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  unfold localOrientationHomologyStalkMap
  infer_instance


def constantToLocalOrientationHomologySheaf :
    𝓒(X; ℚ) ⟶
      singularChainHomologySheaf ℚ X n :=
  TopCat.Sheaf.constantSheafMapOfLocallyRepresentable _ (AddCommGrpCat.of ℚ)
    (localOrientationHomologyStalkMap X n o)
    (localOrientationHomologyStalkMap_locallyRepresentable X n o)


def localOrientationHomologySheafIso :
    𝓒(X; ℚ) ≅
      singularChainHomologySheaf ℚ X n :=
  letI : IsIso (constantToLocalOrientationHomologySheaf X n o) := by
    unfold constantToLocalOrientationHomologySheaf
    exact TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_isIso
      (singularChainHomologySheaf ℚ X n)
      (AddCommGrpCat.of ℚ)
      (localOrientationHomologyStalkMap X n o)
      (localOrientationHomologyStalkMap_locallyRepresentable X n o)
      (localOrientationHomologyStalkMap_isIso X n o)
  asIso (constantToLocalOrientationHomologySheaf X n o)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in

@[reassoc]
theorem localOrientationHomologySheafIso_stalk (x : X) :
    (TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of X)
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (localOrientationHomologySheafIso X n o).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ X
        x n).hom =
      AddCommGrpCat.ofHom
        ((LinearMap.toSpanSingleton ℚ _ (o.generator x)).toAddMonoidHom) := by
  change _ ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (constantToLocalOrientationHomologySheaf X n o).hom ≫ _ = _
  unfold constantToLocalOrientationHomologySheaf
  rw [← Category.assoc]
  erw [TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_stalk]
  unfold localOrientationHomologyStalkMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]


theorem localOrientationHomologySheafIso_stalk_one (x : X) :
    ((TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of X)
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (localOrientationHomologySheafIso X n o).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ X
        x n).hom) 1 = o.generator x := by
  rw [localOrientationHomologySheafIso_stalk]
  exact LinearMap.toSpanSingleton_apply_one ℚ _ (o.generator x)

theorem relative_local_values_constant [PreconnectedSpace X]
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens X) : Set X)ᶜ : Set X)) n) :
    ∃ q : ℚ, ∀ y : X,
      relativeHomologyMap ℚ n
          (supportInclusionPairMap X
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
        q • o.generator y := by
  let e := localOrientationHomologySheafIso X n o
  let s := relativeHomologyToHomologySheafSection ℚ X ⊤ n w
  let t := e.inv.hom.app (op ⊤) s
  obtain ⟨a, ha⟩ := HodgeLean.RealDefs.exists_eq_constSection
    (T := X) (AddCommGrpCat.of ℚ) t
  refine ⟨a, fun y => ?_⟩
  have hs : s = e.hom.hom.app (op ⊤) t := by
    change s = (e.inv.hom ≫ e.hom.hom).app (op ⊤) s
    rw [← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    rfl
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X ⊤ y (Opens.mem_top y) n) w
  have hstalk := ConcreteCategory.congr_hom (localOrientationHomologySheafIso_stalk X n o y) a
  simp only [ConcreteCategory.comp_apply] at hgerm hstalk
  have hgerm' : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
      (singularChainHomologySheafStalkIso ℚ X y n).hom
        ((singularChainHomologySheaf ℚ X n).presheaf.germ ⊤ y (Opens.mem_top y) s) :=
    hgerm.symm
  rw [hgerm', hs, ha]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y (Opens.mem_top y) e.hom.hom]
  erw [HodgeLean.RealDefs.germ_constSection_eq_constantSheafStalkIso]
  erw [hstalk]
  rfl

theorem local_values_constant [PreconnectedSpace X] (c : Homology ℚ X n) :
    ∃ q : ℚ, ∀ y, localOrientation X n c y = q • o.generator y := by
  let A := TopPair.ofSubset ((((⊤ : Opens X) : Set X)ᶜ) : Set X)
  obtain ⟨q, hq⟩ := relative_local_values_constant X n o
    ((relativeHomologyProjection ℚ A n).hom c)
  refine ⟨q, fun y => ?_⟩
  have hn := relativeHomologyProjection_map n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) c
  have hi : (supportInclusionPairMap X
      (Set.singleton_subset_iff.mpr (Opens.mem_top y))).hom.right = 𝟙 X := rfl
  rw [hi] at hn
  erw [homologyMap_id] at hn
  exact hn.symm.trans (hq y)

#print axioms localOrientationHomologySheafIso
#print axioms relative_local_values_constant
#print axioms local_values_constant

end HodgeLean.Foundations.QuotientDuality
