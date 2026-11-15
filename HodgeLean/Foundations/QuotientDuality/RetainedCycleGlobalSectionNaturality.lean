import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalSectionCycle

noncomputable section
open CategoryTheory CochainComplex.HomComplex HomologicalComplex TopologicalSpace Opposite
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inverse integer-constant section coordinates commute with every sheaf morphism. -/
theorem retained_integer_section_inverse_naturality
    (X : TopCat.{0}) {F G : TopCat.Sheaf AddCommGrpCat X} (f : F ⟶ G)
    (s : F.presheaf.obj (op (⊤ : Opens X))) :
    (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections G).symm
        (f.hom.app (op ⊤) s) =
      (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).symm s ≫ f := by
  apply (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections G).injective
  rw [AddEquiv.apply_symm_apply, TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality,
    AddEquiv.apply_symm_apply]

/-- The canonical actual global-section cocycle commutes with postcomposition by every chain map of sheaves. -/
theorem retained_global_section_cycle_cocycle_postcomp
    (X : TopCat.{0}) {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ}
    (f : K ⟶ L) (n : ℤ) (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    retainedGlobalSectionCycleCocycle X L n
        ((cyclesMap (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map f) n).hom z) =
      (retainedGlobalSectionCycleCocycle X K n z).postcomp f := by
  let g := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map f
  have h := ConcreteCategory.congr_hom (cyclesMap_i g n) z
  change (TopCat.Sheaf.globalSectionsComplexInt X L).iCycles n ((cyclesMap g n).hom z) =
    (f.f n).hom.app (op ⊤) ((TopCat.Sheaf.globalSectionsComplexInt X K).iCycles n z) at h
  apply Subtype.ext
  change (retainedGlobalSectionCycleCocycle X L n ((cyclesMap g n).hom z)).1 =
    (retainedGlobalSectionCycleCocycle X K n z).1.comp (Cochain.ofHom f) (add_zero n)
  rw [retained_global_section_cycle_cocycle_from_single,
    retained_global_section_cycle_cocycle_from_single, h,
    retained_integer_section_inverse_naturality, Cochain.fromSingleMk_postcomp]

local instance retainedGlobalSectionNaturalityDerivedCategory (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _

/-- The actual global-section derived comparison is natural under chain maps on every represented cycle. -/
theorem retained_global_sections_derived_comparison_cycle_naturality
    (X : TopCat.{0}) {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ}
    (f : K ⟶ L) (n : ℤ) (z : (TopCat.Sheaf.globalSectionsComplexInt X K).cycles n) :
    retainedGlobalSectionsDerivedComparison X L n
        ((TopCat.Sheaf.globalSectionsComplexInt X L).homologyπ n
          ((cyclesMap (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
            (.up ℤ)).map f) n).hom z)) =
      retainedGlobalSectionsDerivedComparison X K n
        ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n z) ≫
          (DerivedCategory.Q.map f)⟦n⟧' := by
  rw [retained_global_sections_derived_comparison_cycle,
    retained_global_sections_derived_comparison_cycle,
    retained_global_section_cycle_cocycle_postcomp, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Category.assoc]
  have h := (DerivedCategory.Q.commShiftIso n).hom.naturality f
  change DerivedCategory.Q.map (f⟦n⟧') ≫ (DerivedCategory.Q.commShiftIso n).hom.app L =
    (DerivedCategory.Q.commShiftIso n).hom.app K ≫ (DerivedCategory.Q.map f)⟦n⟧' at h
  rw [h]
  simp only [Category.assoc]

/-- The canonical actual global-section derived comparison is natural on all homology classes under every chain map of sheaves. -/
theorem retained_global_sections_derived_comparison_naturality
    (X : TopCat.{0}) {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ}
    (f : K ⟶ L) (n : ℤ) (a : (TopCat.Sheaf.globalSectionsComplexInt X K).homology n) :
    retainedGlobalSectionsDerivedComparison X L n
        ((HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
            (.up ℤ)).map f) n).hom a) =
      retainedGlobalSectionsDerivedComparison X K n a ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  let g := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
    (.up ℤ)).map f
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n)).mp inferInstance a
  have h := ConcreteCategory.congr_hom (homologyπ_naturality g n) z
  change (HomologicalComplex.homologyMap g n).hom
      ((TopCat.Sheaf.globalSectionsComplexInt X K).homologyπ n z) =
    (TopCat.Sheaf.globalSectionsComplexInt X L).homologyπ n ((cyclesMap g n).hom z) at h
  rw [h]
  exact retained_global_sections_derived_comparison_cycle_naturality X f n z

end HodgeLean.Foundations.QuotientDuality
