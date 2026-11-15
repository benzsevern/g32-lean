import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs

/-! Isomorphisms on the actual point-complement pairs of a homeomorphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

def localPointHomeomorphPairIso (H : M ≃ₜ N) (x : M) :
    pointComplementPair x ≅ pointComplementPair (H x) where
  hom := pointComplementHomeomorphPairMap H x
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨H.symm, H.symm.continuous⟩)
    (TopCat.ofHom ⟨fun y => ⟨H.symm y, fun he => y.2 (by
      exact (H.apply_symm_apply y.val).symm.trans (congrArg H he))⟩,
      (H.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      exact H.symm_apply_apply z.val
    · ext z
      exact H.symm_apply_apply z
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      exact H.apply_symm_apply z.val
    · ext z
      exact H.apply_symm_apply z

theorem pointComplement_homeomorph_homology_bijective (H : M ≃ₜ N) (x : M) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)) := by
  change Function.Bijective
    (((relativeHomologyFunctor ℚ n).map (localPointHomeomorphPairIso H x).hom).hom)
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

#print axioms localPointHomeomorphPairIso
#print axioms pointComplement_homeomorph_homology_bijective
end HodgeLean.Foundations.QuotientDuality
