import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapBoundaryHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Localization of an actual Hom-complex cohomology class, with its specified shift comparison. -/
def retainedHomCohomologyDerivedComparison (K L : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass K L n →+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  CohomologyClass.descAddMonoidHom
    { toFun := fun z => DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L
      map_zero' := by simp
      map_add' := by intro a b; simp [Preadditive.add_comp] }
    (by
      rintro ⟨z, hz⟩ ⟨m, hm, β, hβ⟩
      change DerivedCategory.Q.map (Cocycle.equivHomShift.symm ⟨z, hz⟩) ≫ _ = 0
      rw [retained_derived_shift_hom_zero_of_boundary m n hm ⟨z, hz⟩ β hβ, zero_comp])

/-- A represented Hom-complex class localizes to its literal shifted cocycle morphism. -/
theorem retained_hom_cohomology_derived_comparison_on_class
    (K L : CochainComplex C ℤ) (n : ℤ) (z : Cocycle K L n) :
    retainedHomCohomologyDerivedComparison K L n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := rfl

/-- Localization of actual Hom-complex classes is bijective into a K-injective target. -/
theorem retained_hom_cohomology_derived_comparison_bijective
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    Function.Bijective (retainedHomCohomologyDerivedComparison K L n) := by
  let e := Iso.homCongr ((DerivedCategory.quotientCompQhIso C).symm.app K)
    ((DerivedCategory.Q.commShiftIso n).symm.app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app (L⟦n⟧))
  have he : e ∘ (retainedHomCohomologyDerivedComparison K L n : _ → _) =
      DerivedCategory.Qh.map ∘ (CohomologyClass.toHom (K := K) (L := L) (n := n)) := by
    funext a
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective a
    rw [Function.comp_apply, retained_hom_cohomology_derived_comparison_on_class]
    simp [e, CohomologyClass.toHom_mk]
  have hb := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) (L⟦n⟧)).comp
      (CohomologyClass.toHom_bijective K L n)
  rw [← he] at hb
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp hb

end HodgeLean.Foundations.QuotientDuality
