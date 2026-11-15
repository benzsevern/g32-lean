import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericEtaleOpen

/-! # Actual affine finite etale generic neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual generic finite etale base neighborhood can be chosen affine while retaining the original generic point and original restricted morphism.
Source: Stacks Project, Tag 02UP; the affine-open basis and base change of finite etale morphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_generically_finite_etale_affine_open
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left)) :
    ∃ U : Y.left.Opens, IsAffineOpen U ∧ genericPoint Y.left ∈ U ∧
      IsFinite (f.left ∣_ U) ∧ Etale (f.left ∣_ U) := by
  obtain ⟨U, hUdense, hfinite, hetale⟩ := properCycle_generically_finite_etale_base_open f hg hdegree
  obtain ⟨y, hy⟩ := hUdense.nonempty
  have hUg : genericPoint Y.left ∈ U :=
    (genericPoint_specializes y).mem_open U.isOpen hy
  obtain ⟨W, hW, hgW, hWU⟩ := exists_isAffineOpen_mem_and_subset hUg
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    change U ⊓ W = W
    exact inf_eq_right.mpr hWU
  letI : IsFinite (f.left ∣_ U) := hfinite
  letI : Etale (f.left ∣_ U) := hetale
  have hfW : IsFinite (f.left ∣_ W) := by
    rw [← hVW]
    exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f.left U V)).mp inferInstance
  have heW : Etale (f.left ∣_ W) := by
    rw [← hVW]
    exact (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictRestrict f.left U V)).mp inferInstance
  exact ⟨W, hW, hgW, hfW, heW⟩

end HodgeLean.Foundations.QuotientDuality
