import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedHomComparison

noncomputable section
open CategoryTheory CochainComplex.HomComplex
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical Hom-complex homology equivalence sends an actual cycle projection to its represented cocycle class. -/
theorem retained_hom_complex_cycle_class_projection
    {C : Type*} [Category C] [Abelian C]
    (K L : CochainComplex C ℤ) (n : ℤ) (z : (CochainComplex.HomComplex K L).cycles n) :
    homologyAddEquiv K L n (((CochainComplex.HomComplex K L).homologyπ n).hom z) =
      CohomologyClass.mk (((leftHomologyData K L n).cyclesIso.hom).hom z) := by
  exact ConcreteCategory.congr_hom
    ((leftHomologyData K L n).homologyπ_comp_homologyIso_hom) z

/-- The chosen Hom-complex cycle coordinates retain the literal underlying cochain of the actual cycle. -/
theorem retained_hom_complex_cycle_cocycle_coe
    {C : Type*} [Category C] [Abelian C]
    (K L : CochainComplex C ℤ) (n : ℤ) (z : (CochainComplex.HomComplex K L).cycles n) :
    (show Cocycle K L n from (((leftHomologyData K L n).cyclesIso.hom).hom z)).1 =
      ((CochainComplex.HomComplex K L).iCycles n).hom z := by
  exact ConcreteCategory.congr_hom ((leftHomologyData K L n).cyclesIso_hom_comp_i) z

end HodgeLean.Foundations.QuotientDuality
