import HodgeLean.Foundations.QuotientDuality.RetainedCycleSoftDerivedComparison
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePlusHomologyComparison
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # The right-derived section unit on bounded soft models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance softSectionsSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _
local instance softSectionsGroupDerived : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- The actual right-derived unit for global sections is invertible on every bounded soft complex. -/
theorem retained_soft_global_sections_unit_isIso
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat X))
    (hK : ∀ i, IsSoft (K.obj.X i)) :
    IsIso ((subdivisionGlobalSectionsFunctor X).rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, hb⟩ := K.property
  letI : K.obj.IsStrictlyGE b := hb
  obtain ⟨L, hL, f, hf⟩ := CochainComplex.Plus.exists_quasiIso_injective K b
  let I := (InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat X)).mapCochainComplexPlus.obj L
  letI : L.obj.IsStrictlyGE b := hL
  haveI : I.obj.IsStrictlyGE b := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat X)).mapHomologicalComplex
        (.up ℤ)).obj L.obj) b
    rwa [CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff]
  letI : QuasiIso f.hom := hf
  have hs (i : ℤ) : IsSoft (I.obj.X i) := by
    haveI : Injective (I.obj.X i) := (L.obj.X i).property
    letI := TopCat.Sheaf.injective_isFlasque X (I.obj.X i)
    exact HodgeLean.Foundations.spec_isSoft_of_isFlasque _
  let F := subdivisionGlobalSectionsFunctor X
  let g := F.mapCochainComplexPlus.map f
  haveI : QuasiIso g.hom := bounded_soft_global_quasiIso X f.hom b b hf hK hs
  haveI : IsIso (DerivedCategory.Plus.Q.map g) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso AddCommGrpCat) _
      (show QuasiIso g.hom from inferInstance)
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
    dsimp only [I]
    infer_instance
  haveI : IsIso (DerivedCategory.Plus.Q.map f) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (TopCat.Sheaf AddCommGrpCat X)) _ hf
  haveI : IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
    infer_instance
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
    have hn := F.rightDerivedFunctorPlusUnit.naturality f
    change DerivedCategory.Plus.Q.map g ≫ F.rightDerivedFunctorPlusUnit.app I =
      F.rightDerivedFunctorPlusUnit.app K ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) at hn
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.rightDerivedFunctorPlusUnit.app K)
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))

/-- A nonzero comparison image remains nonzero under the original right-derived unit. -/
theorem retained_derived_sections_unit_nonzero_of_comparison
    {C : Type*} [Category C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]
    (F : C ⥤ AddCommGrpCat) [F.Additive]
    (K L : CochainComplex.Plus C) (f : K ⟶ L)
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)))
    (ha : ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f))).hom a ≠ 0) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
      (F.rightDerivedFunctorPlusUnit.app K)).hom a ≠ 0 := by
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat n
  have hn : DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
      F.rightDerivedFunctorPlusUnit.app L =
      F.rightDerivedFunctorPlusUnit.app K ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) :=
    F.rightDerivedFunctorPlusUnit.naturality f
  have he := ConcreteCategory.congr_hom (congrArg (fun g => H.map g) hn) a
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at he
  change (H.map (F.rightDerivedFunctorPlusUnit.app L)).hom
      ((H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f))).hom a) =
    (H.map (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))).hom
      ((H.map (F.rightDerivedFunctorPlusUnit.app K)).hom a) at he
  intro hz
  change (H.map (F.rightDerivedFunctorPlusUnit.app K)).hom a = 0 at hz
  rw [hz, map_zero] at he
  exact ha ((ConcreteCategory.bijective_of_isIso
    (H.map (F.rightDerivedFunctorPlusUnit.app L))).1
      (he.trans (map_zero _).symm))

/-- A homology-isomorphic comparison into a unit-invertible model detects the original unit injectively. -/
theorem retained_derived_sections_unit_injective_of_comparison
    {C : Type*} [Category C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]
    (F : C ⥤ AddCommGrpCat) [F.Additive]
    (K L : CochainComplex.Plus C) (f : K ⟶ L)
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (n : ℤ) [QuasiIsoAt (F.mapCochainComplexPlus.map f).hom n] :
    Function.Injective ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
      (F.rightDerivedFunctorPlusUnit.app K)).hom := by
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat n
  letI := retained_plus_homology_map_isIso (F.mapCochainComplexPlus.map f) n
  have hinj := (ConcreteCategory.bijective_of_isIso
    (H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)))).1
  intro a b hab
  by_contra h
  have hz : (H.map (F.rightDerivedFunctorPlusUnit.app K)).hom (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hn : (H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f))).hom
      (a-b) ≠ 0 := by
    intro hh
    exact (sub_ne_zero.mpr h) (hinj (hh.trans (map_zero _).symm))
  exact (retained_derived_sections_unit_nonzero_of_comparison F K L f n (a-b) hn) hz

end HodgeLean.Foundations.QuotientDuality
