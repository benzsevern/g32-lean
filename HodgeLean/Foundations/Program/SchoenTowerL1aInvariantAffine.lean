import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantReduced

/-! # Affineness of the invariant-ring structure map

The glued invariant-ring construction is affine over its specified base.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency.types false in
/-- The preimage of each base affine is precisely its invariant-ring chart.
Source: Stacks Project, tag 01LH, relative affine gluing and its chart preimages. -/
theorem s2v_l1a_invariantSpaceMap_preimage
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (U : Y.affineOpens) :
    s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U.1 =
      ((s2v_l1a_invariantSpaceCover f a ha).f U).opensRange := by
  simpa using! (s2v_l1a_invariantGlueData f a ha).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The invariant-ring structure morphism is affine over the specified base.
Source: Stacks Project, tag 01LH, relative affine gluing. -/
theorem s2v_l1a_invariantSpaceMap_affine
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    IsAffineHom (s2v_l1a_invariantSpaceMap f a ha) := by
  constructor
  intro U hU
  rw [s2v_l1a_invariantSpaceMap_preimage f a ha ⟨U, hU⟩]
  have hAff : IsAffine ((s2v_l1a_invariantSpaceCover f a ha).X ⟨U, hU⟩) := by
    change IsAffine (Spec (CommRingCat.of (s2v_l1a_fixedSectionSubring f a ha U)))
    infer_instance
  exact @isAffineOpen_opensRange _ _ hAff
    ((s2v_l1a_invariantSpaceCover f a ha).f (⟨U, hU⟩ : Y.AffineZariskiSite)) inferInstance

end HodgeLean.Foundations.Program
