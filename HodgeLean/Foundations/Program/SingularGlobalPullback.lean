module

public import HodgeLean.Foundations.Program.SingularCochainSheafPullback
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.GlobalRestriction
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueExtendNat

@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Ordinary rational singular cochains map to the actual global singular sheaf sections. -/
def singularGlobalComparison (X : TopCat.{0}) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (SingularCochainComplex ℚ X) ⟶ globalSingularCochainSheafComplex ℚ X :=
  ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexIsoTopOpen ℚ X).hom ≫
    (globalRawSingularCochainComplexIso ℚ X).inv ≫
      topOpenToGlobalSingularCochainSheafComplex ℚ X

/-- The ordinary-to-global rational cochain comparison is a quasi-isomorphism. -/
theorem singularGlobalComparison_quasiIso (X : TopCat.{0})
    [ParacompactSpace X] [T2Space X] : QuasiIso (singularGlobalComparison X) := by
  letI : QuasiIso (topOpenToGlobalSingularCochainSheafComplex ℚ X) :=
    topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := X)
  haveI : QuasiIso (((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex
      (.up ℕ)).map (singularCochainComplexIsoTopOpen ℚ X).hom) := inferInstance
  haveI : QuasiIso (globalRawSingularCochainComplexIso ℚ X).inv := inferInstance
  unfold singularGlobalComparison
  rw [quasiIso_iff_comp_left, quasiIso_iff_comp_left]
  exact topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := X)

/-- The global comparison sends an ordinary cochain to its actual sheafification. -/
theorem singularGlobalComparison_apply (X : TopCat.{0}) (n : ℕ)
    (φ : Module.Dual ℚ ((SingularChainComplex ℚ X).X n)) :
    (singularGlobalComparison X).f n φ =
      (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℚ X n)).app
        (op ⊤) (φ.comp ((topOpenSingularChainComplexIso ℚ X).hom.f n).hom) := by
  simp only [singularGlobalComparison, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

/-- Actual singular sheaf pullback induces a map on global sections. -/
def singularGlobalSheafPullback {A B : TopCat.{0}} (q : A ⟶ B) :
    globalSingularCochainSheafComplex ℚ B ⟶ globalSingularCochainSheafComplex ℚ A :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor B).mapHomologicalComplex
    (.up ℕ)).map
      (singularCochainSheafComplexPullback ℚ q)

/-- The top-open chain identifications commute with the actual point map. -/
theorem singularOpenChainMap_top {A B : TopCat.{0}} (q : A ⟶ B) :
    (singularOpenChainMap ℚ q).app ⊤ ≫ (topOpenSingularChainComplexIso ℚ B).hom =
      (topOpenSingularChainComplexIso ℚ A).hom ≫ singularChainComplexMap ℚ q := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)
  change F.map ((openPreimageToTarget q).app ⊤) ≫ F.map (Opens.inclusionTopIso B).hom =
    F.map (Opens.inclusionTopIso A).hom ≫ F.map q
  rw [← F.map_comp, ← F.map_comp]
  congr 1

/-- The global sheaf comparison commutes with actual ordinary singular pullback. -/
theorem singularGlobalComparison_naturality {A B : TopCat.{0}} (q : A ⟶ B) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ q) ≫ singularGlobalComparison A =
      singularGlobalComparison B ≫ singularGlobalSheafPullback q := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext φ
  change Module.Dual ℚ ((SingularChainComplex ℚ B).X n) at φ
  change (singularGlobalComparison A).f n ((singularCochainComplexMap ℚ q).f n φ) =
    (singularCochainSheafPullback ℚ q n).hom.app (op ⊤)
      ((singularGlobalComparison B).f n φ)
  rw [singularGlobalComparison_apply, singularGlobalComparison_apply]
  have hu := congrArg (fun v => v.app (op ⊤)) (singularCochainSheafPullback_unit ℚ q n)
  have hv := congrArg (fun v => v.hom (φ.comp ((topOpenSingularChainComplexIso ℚ B).hom.f n).hom)) hu
  change (singularCochainSheafPullback ℚ q n).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology B) (singularCochainPresheaf ℚ B n)).app
        (op ⊤) (φ.comp ((topOpenSingularChainComplexIso ℚ B).hom.f n).hom)) =
    (toSheafify (Opens.grothendieckTopology A) (singularCochainPresheaf ℚ A n)).app
      (op ⊤) ((φ.comp ((topOpenSingularChainComplexIso ℚ B).hom.f n).hom).comp
        (((singularOpenChainMap ℚ q).app ⊤).f n).hom) at hv
  rw [hv]
  congr 1
  apply LinearMap.ext
  intro z
  exact congrArg (fun f => φ ((f.f n).hom z)) (singularOpenChainMap_top q).symm

end HodgeLean.Foundations.Program
