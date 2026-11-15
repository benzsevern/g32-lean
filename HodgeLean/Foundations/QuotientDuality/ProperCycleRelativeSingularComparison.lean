import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedSheaf
import HodgeLean.Foundations.QuotientDuality.ProperCycleShiftedDerivedSupport

/-! # Fixed relative singular comparison for original supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

private def wholePairIso (Y : TopCat.{0}) (S : Set Y) :
    neighborhoodSupportComplementPair (Set.univ : Set Y) S ≅ TopPair.ofSubset Sᶜ where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.val.val, z.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) rfl
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨fun z => ⟨z, Set.mem_univ _⟩, continuous_id.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun z => ⟨⟨z.val, Set.mem_univ _⟩, z.property⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩) rfl
  hom_inv_id := by apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  inv_hom_id := by apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl

/-- The fixed relative singular comparison uses the constant augmentation and the identity on underlying points of the whole-space pair.
Source: Bredon, Sheaf Theory, III.1; properCycle_supported_cohomology_presheaf_iso.
HC no distance; AV milestone no distance. -/
def properCycle_relative_singular_comparison
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (S : Closeds (a3b4_an X.hom)) (n : ℕ) :
    AddCommGrpCat.of (TopCat.Sheaf.supportH (a3b4_an X.hom) S
      (TopCat.Sheaf.const (a3b4_an X.hom) (AddCommGrpCat.of ℚ)) n) ≅
      AddCommGrpCat.of (RelativeCohomology ℚ (TopPair.ofSubset (S : Set (a3b4_an X.hom))ᶜ) n) := by
  let Y := a3b4_an X.hom
  letI : T2Space Y := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : ∀ V : Opens Y, ParacompactSpace V := properCycle_open_paracompact X
  let e := (ComplexPoint.rationalSupportAddEquivSupportedInjectiveHomology X S n).trans
    ((supportedSingularInjectiveHomologyIso Y
      (properCycle_contractible_open_basis X) S.compl ⊤ (n : ℤ)).symm.addCommGroupIsoToAddEquiv)
      |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
        Y S S.isClosed ⊤ n)
  let e' : RelativeCohomology ℚ (neighborhoodSupportComplementPair (Set.univ : Set Y) S) n ≃+
      RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) n :=
    ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso
        (wholePairIso Y S).symm))).toLinearEquiv.toAddEquiv
  exact (e.trans e').toAddCommGrpIso

example (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (S : Closeds (a3b4_an X.hom)) (n : ℕ) :
    (properCycle_relative_singular_comparison X S n).hom 0 = 0 := map_zero _

end HodgeLean.Foundations.QuotientDuality
