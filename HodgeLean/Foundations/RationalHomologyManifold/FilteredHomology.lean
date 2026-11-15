import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! Canonical homology comparisons for exact colimits of chain diagrams.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

variable {J C : Type*} [Category* J] [Category* C] [Abelian C]

/-- Homology of a diagram-valued short complex agrees naturally with the diagram of homology objects.
HC no distance; AV milestone no distance.
-/
def diagramHomologyIso (F : J ⥤ ShortComplex C) :
    F ⋙ ShortComplex.homologyFunctor C ≅
      ((ShortComplex.functorEquivalence J C).inverse.obj F).homology := by
  let S := (ShortComplex.functorEquivalence J C).inverse.obj F
  refine NatIso.ofComponents
    (fun j => S.mapHomologyIso ((evaluation J C).obj j)) ?_
  intro j k f
  change ShortComplex.homologyMap (S.mapNatTrans ((evaluation J C).map f)) ≫
      (S.mapHomologyIso ((evaluation J C).obj k)).hom =
    (S.mapHomologyIso ((evaluation J C).obj j)).hom ≫
      ((evaluation J C).map f).app S.homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms diagramHomologyIso
/-- Exact colimits commute canonically with the homology of short complexes.
HC no distance; AV milestone no distance.
-/
def shortComplexColimitHomologyIso [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ ShortComplex C) :
    colimit (F ⋙ ShortComplex.homologyFunctor C) ≅ (colimit F).homology := by
  let S := (ShortComplex.functorEquivalence J C).inverse.obj F
  let eS : S.map (colim : (J ⥤ C) ⥤ C) ≅ colimit F :=
    (ShortComplex.isColimitColimitCocone F).coconePointUniqueUpToIso (colimit.isColimit F)
  exact ((colim : (J ⥤ C) ⥤ C).mapIso (diagramHomologyIso F)) ≪≫
    (S.mapHomologyIso (colim : (J ⥤ C) ⥤ C)).symm ≪≫
      ShortComplex.homologyMapIso eS

#print axioms shortComplexColimitHomologyIso
/-- The exact-colimit homology comparison retains the canonical maps from each diagram object.
HC no distance; AV milestone no distance.
-/
theorem shortComplexColimitHomologyIso_ι [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ ShortComplex C) (j : J) :
    colimit.ι (F ⋙ ShortComplex.homologyFunctor C) j ≫
      (shortComplexColimitHomologyIso F).hom = ShortComplex.homologyMap (colimit.ι F j) := by
  let S := (ShortComplex.functorEquivalence J C).inverse.obj F
  let eS : S.map (colim : (J ⥤ C) ⥤ C) ≅ colimit F :=
    (ShortComplex.isColimitColimitCocone F).coconePointUniqueUpToIso (colimit.isColimit F)
  have hfac : S.mapNatTrans (colim.ι j) ≫ eS.hom = colimit.ι F j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (ShortComplex.isColimitColimitCocone F) (colimit.isColimit F) j
  change colimit.ι (F ⋙ ShortComplex.homologyFunctor C) j ≫
      (colim.map (diagramHomologyIso F).hom ≫
        (S.mapHomologyIso (colim : (J ⥤ C) ⥤ C)).inv ≫ ShortComplex.homologyMap eS.hom) = _
  calc
    _ = ((S.mapHomologyIso ((evaluation J C).obj j)).hom ≫ colimit.ι S.homology j ≫
        (S.mapHomologyIso (colim : (J ⥤ C) ⥤ C)).inv) ≫ ShortComplex.homologyMap eS.hom := by
      simp only [colimit.ι_map_assoc, diagramHomologyIso, Category.assoc]
      rfl
    _ = ShortComplex.homologyMap (S.mapNatTrans (colim.ι j)) ≫
        ShortComplex.homologyMap eS.hom := by
      rw [ShortComplex.homologyMap_mapNatTrans]
      rfl
    _ = _ := by rw [← ShortComplex.homologyMap_comp, hfac]

#print axioms shortComplexColimitHomologyIso_ι
/-- Homology preserves each diagram whose colimits are exact.
HC no distance; AV milestone no distance.
-/
theorem shortComplexHomology_preservesColimit [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] (F : J ⥤ ShortComplex C) :
    PreservesColimit F (ShortComplex.homologyFunctor C) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.homologyFunctor C))
  exact Cocone.ext (shortComplexColimitHomologyIso F)
    (fun j => shortComplexColimitHomologyIso_ι F j)

#print axioms shortComplexHomology_preservesColimit
/-- Taking the short complex at a degree preserves diagram colimits.
HC no distance; AV milestone no distance.
-/
theorem shortComplexFunctor_preservesColimit {ι : Type*} (c : ComplexShape ι) (n : ι)
    [HasColimitsOfShape J C] (F : J ⥤ HomologicalComplex C c) :
    PreservesColimit F (HomologicalComplex.shortComplexFunctor C c n) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply ShortComplex.isColimitOfIsColimitπ
  · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.prev n)) (colimit.isColimit F)
  · exact isColimitOfPreserves (HomologicalComplex.eval C c n) (colimit.isColimit F)
  · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.next n)) (colimit.isColimit F)

#print axioms shortComplexFunctor_preservesColimit
/-- Homology in each degree preserves exact diagram colimits of complexes.
HC no distance; AV milestone no distance.
-/
theorem complexHomology_preservesColimit {ι : Type*} (c : ComplexShape ι) (n : ι)
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ HomologicalComplex C c) :
    PreservesColimit F (HomologicalComplex.homologyFunctor C c n) := by
  let S := HomologicalComplex.shortComplexFunctor C c n
  letI : PreservesColimit F S := shortComplexFunctor_preservesColimit c n F
  letI : PreservesColimit (F ⋙ S) (ShortComplex.homologyFunctor C) :=
    shortComplexHomology_preservesColimit (F ⋙ S)
  exact inferInstanceAs (PreservesColimit F (S ⋙ ShortComplex.homologyFunctor C))

#print axioms complexHomology_preservesColimit
end HodgeLean.Foundations.RationalHomologyManifold
