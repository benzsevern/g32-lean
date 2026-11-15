import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Canonical homology coordinates for bounded derived complexes -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original localization comparisons identify bounded derived homology with ordinary homology. -/
def retainedPlusHomologyComparison
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIso C) (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.homologyFunctorFactors C n)

/-- A quasi-isomorphism in one actual degree induces an isomorphism in bounded derived homology. -/
lemma retained_plus_homology_map_isIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex.Plus C} (f : K ⟶ L) (n : ℤ) [QuasiIsoAt f.hom n] :
    IsIso ((DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f)) := by
  let e := retainedPlusHomologyComparison C n
  haveI : IsIso (HomologicalComplex.homologyMap f.hom n) := by infer_instance
  have hn := e.hom.naturality f
  change (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
      e.hom.app L = e.hom.app K ≫ HomologicalComplex.homologyMap f.hom n at hn
  haveI : IsIso ((DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
      e.hom.app L) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f)) (e.hom.app L)

/-- Nonzero ordinary homology images stay nonzero in the specified bounded derived coordinates. -/
lemma retained_plus_homology_inverse_map_nonzero
    [HasDerivedCategory AddCommGrpCat]
    {K L : CochainComplex.Plus AddCommGrpCat} (f : K ⟶ L) (n : ℤ)
    (a : K.obj.homology n)
    (ha : HomologicalComplex.homologyMap f.hom n a ≠ 0) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map (DerivedCategory.Plus.Q.map f))
      (((retainedPlusHomologyComparison AddCommGrpCat n).inv.app K) a) ≠ 0 := by
  let e := retainedPlusHomologyComparison AddCommGrpCat n
  have he := ConcreteCategory.congr_hom (e.hom.naturality f) ((e.inv.app K) a)
  simp only [ConcreteCategory.comp_apply] at he
  have hid := ConcreteCategory.congr_hom (e.inv_hom_id_app K) a
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hid
  rw [hid] at he
  change (e.hom.app L).hom
    (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
      (DerivedCategory.Plus.Q.map f)).hom ((e.inv.app K).hom a)) =
      (HomologicalComplex.homologyMap f.hom n).hom a at he
  intro hz
  change ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    (DerivedCategory.Plus.Q.map f)).hom ((e.inv.app K).hom a) = 0 at hz
  rw [hz, map_zero] at he
  exact ha he.symm

end HodgeLean.Foundations.QuotientDuality
