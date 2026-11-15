import HodgeLean.Foundations.QuotientDuality.RetainedCycleHomComplexCycleClass
import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalDerivedComparison

noncomputable section
open CategoryTheory CochainComplex.HomComplex HomologicalComplex
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical Hom-complex cocycle of an actual cycle in global sections. -/
def retainedGlobalSectionCycleCocycle (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ)
    (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    Cocycle (TopCat.Sheaf.integerConstantSingleComplex X) K n :=
  (((leftHomologyData (TopCat.Sheaf.integerConstantSingleComplex X) K n).cyclesIso.hom).hom)
    ((cyclesMap (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).inv n).hom z)

local instance retainedGlobalSectionCycleDerivedCategory (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _

/-- The actual global-section comparison on a represented cycle is the localization of its canonical literal shifted cocycle morphism. -/
theorem retained_global_sections_derived_comparison_cycle
    (X : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ)
    (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    retainedGlobalSectionsDerivedComparison X K n
        ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm (retainedGlobalSectionCycleCocycle X K n z)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K := by
  let e := TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K
  change retainedHomCohomologyDerivedComparison (TopCat.Sheaf.integerConstantSingleComplex X) K n
    (homologyAddEquiv (TopCat.Sheaf.integerConstantSingleComplex X) K n
      ((HomologicalComplex.homologyMap e.inv n).hom
        ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n z))) = _
  have h := ConcreteCategory.congr_hom (homologyπ_naturality e.inv n) z
  change (HomologicalComplex.homologyMap e.inv n).hom
      ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n z) =
    (CochainComplex.HomComplex (TopCat.Sheaf.integerConstantSingleComplex X) K).homologyπ n
      ((cyclesMap e.inv n).hom z) at h
  rw [h, retained_hom_complex_cycle_class_projection]
  exact retained_hom_cohomology_derived_comparison_on_class
    (TopCat.Sheaf.integerConstantSingleComplex X) K n (retainedGlobalSectionCycleCocycle X K n z)

/-- The canonical cocycle of a global-section cycle retains its literal underlying cochain through the inverse global-section isomorphism. -/
theorem retained_global_section_cycle_cocycle_coe
    (X : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ)
    (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    (retainedGlobalSectionCycleCocycle X K n z).1 =
      ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).inv.f n).hom
        ((TopCat.Sheaf.globalSectionsComplexInt X K).iCycles n z) := by
  rw [retainedGlobalSectionCycleCocycle, retained_hom_complex_cycle_cocycle_coe]
  exact ConcreteCategory.congr_hom
    (cyclesMap_i (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).inv n) z

/-- The inverse global-section isomorphism sends a literal section to the single-source cochain of its integer-constant sheaf morphism. -/
theorem retained_global_sections_hom_complex_inverse_component
    (X : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ)
    (s : (TopCat.Sheaf.globalSectionsComplexInt X K).X n) :
    ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).inv.f n).hom s =
      Cochain.fromSingleMk
        ((TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.X n)).symm s) (zero_add n) := by
  rfl

/-- The canonical cocycle of an actual global-section cycle is the literal single-source cochain specified by that section. -/
theorem retained_global_section_cycle_cocycle_from_single
    (X : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ)
    (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    (retainedGlobalSectionCycleCocycle X K n z).1 =
      Cochain.fromSingleMk
        ((TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.X n)).symm
          ((TopCat.Sheaf.globalSectionsComplexInt X K).iCycles n z)) (zero_add n) := by
  rw [retained_global_section_cycle_cocycle_coe, retained_global_sections_hom_complex_inverse_component]

end HodgeLean.Foundations.QuotientDuality
