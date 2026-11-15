import HodgeLean.Foundations.Program.SchoenTowerL1aToInvariantSpace

/-! # Reducedness of the actual invariant-ring scheme

The actual invariant rings inherit reducedness from the reduced source.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The scheme of invariant sections of an affine map from an reduced source is reduced.
Source: Stacks Project, tags 04A9 and 01LH, invariant subrings and relative affine gluing. -/
theorem s2v_l1a_invariantSpace_reduced
    {X Y : Scheme} [AlgebraicGeometry.IsReduced X] {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    AlgebraicGeometry.IsReduced (s2v_l1a_invariantSpace f a ha) := by
  have (i : Y.AffineZariskiSite) :
      AlgebraicGeometry.IsReduced ((s2v_l1a_invariantSpaceCover f a ha).X i) := by
    have : _root_.IsReduced (s2v_l1a_fixedSectionSubring f a ha i.1) :=
      isReduced_of_injective (s2v_l1a_fixedSectionSubring f a ha i.1).subtype
        Subtype.val_injective
    dsimp [s2v_l1a_invariantSpaceCover, s2v_l1a_invariantGlueData,
      Scheme.AffineZariskiSite.relativeGluingData]
    change AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (s2v_l1a_fixedSectionSubring f a ha i.1)))
    infer_instance
  exact .of_openCover _ (s2v_l1a_invariantSpaceCover f a ha)

end HodgeLean.Foundations.Program
