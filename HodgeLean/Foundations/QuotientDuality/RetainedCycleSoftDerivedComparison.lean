import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalSectionNaturality
import HodgeLean.Foundations.RationalHomologyManifold.BoundedSoftQuasiIso
import Mathlib.Algebra.Homology.Factorizations.CM5a

/-! # Derived comparison for bounded soft chain models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance softDerivedCategory (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _

/-- The canonical section comparison is bijective for every bounded-below soft sheaf complex. -/
theorem retained_soft_global_sections_derived_comparison_bijective
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ)
    (b : ℤ) [K.IsStrictlyGE b] (hK : ∀ i, IsSoft (K.X i)) (n : ℤ) :
    Function.Bijective (retainedGlobalSectionsDerivedComparison X K n) := by
  obtain ⟨L, f, hf, hI, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K b
  letI : QuasiIso f := hf
  letI : L.IsStrictlyGE b := hL
  letI (i : ℤ) : Injective (L.X i) := hI i
  letI : L.IsKInjective := CochainComplex.isKInjective_of_injective L b
  have hs (i : ℤ) : IsSoft (L.X i) := by
    letI := TopCat.Sheaf.injective_isFlasque X (L.X i)
    exact HodgeLean.Foundations.spec_isSoft_of_isFlasque _
  let g := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
    (.up ℤ)).map f
  letI : QuasiIso g := bounded_soft_global_quasiIso X f b b hf hK hs
  have hg := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap g n)
  let e := Iso.homCongr (Iso.refl (DerivedCategory.Q.obj
      (TopCat.Sheaf.integerConstantSingleComplex X)))
    (asIso ((DerivedCategory.Q.map f)⟦n⟧'))
  have he : e ∘ (retainedGlobalSectionsDerivedComparison X K n : _ → _) =
      (retainedGlobalSectionsDerivedComparison X L n : _ → _) ∘
        (HomologicalComplex.homologyMap g n).hom := by
    funext a
    simpa only [Function.comp_apply, e, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, asIso_hom] using
      (retained_global_sections_derived_comparison_naturality X f n a).symm
  have hb := (retained_global_sections_derived_comparison_bijective_of_kInjective X L n).comp hg
  rw [← he] at hb
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp hb

end HodgeLean.Foundations.QuotientDuality
