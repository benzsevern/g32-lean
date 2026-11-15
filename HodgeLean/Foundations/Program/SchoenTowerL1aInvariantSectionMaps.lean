import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantAffine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Section maps on the actual invariant-ring charts

The canonical map induces the inclusion of the actual fixed subring.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
variable {X Y : Scheme} {T : Type*} [Finite T]
variable (f : X ⟶ Y) [IsAffineHom f]
variable (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)

set_option backward.isDefEq.respectTransparency.types false in
/-- Sections on an invariant affine chart identify with its actual fixed subring.
Source: Stacks Project, tag 01LH, affine charts in relative gluing. -/
def s2v_l1a_invariantObjIso {U : Y.Opens} (hU : IsAffineOpen U) :
    Γ(s2v_l1a_invariantSpace f a ha, s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U) ≅
      .of (s2v_l1a_fixedSectionSubring f a ha U) :=
  (s2v_l1a_invariantSpace f a ha).presheaf.mapIso (eqToIso
    (by simpa using! (s2v_l1a_invariantSpaceMap_preimage f a ha ⟨U, hU⟩).symm)).op ≪≫
  ((s2v_l1a_invariantSpaceCover f a ha).f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical map pulls sections back by the actual invariant-ring inclusion.
Source: Stacks Project, tags 04A9 and 01LH, invariant functions on glued affine charts. -/
lemma s2v_l1a_toInvariantSpace_app_preimage (U : Y.affineOpens) :
      (s2v_l1a_toInvariantSpace f a ha).app (s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ ↑U) =
      (s2v_l1a_invariantObjIso f a ha U.2).hom ≫
      CommRingCat.ofHom (s2v_l1a_fixedSectionSubring f a ha U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  dsimp [s2v_l1a_invariantObjIso]
  change _ = (s2v_l1a_invariantSpace f a ha).presheaf.map (eqToHom (by simp [s2v_l1a_invariantSpaceMap_preimage])).op ≫
      (((s2v_l1a_invariantSpaceCover f a ha).f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (s2v_l1a_fixedSectionSubring f a ha U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op
  have H : s2v_l1a_toInvariantSpace f a ha ⁻¹ᵁ s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ s2v_l1a_toInvariantSpace f a ha) ⁻¹ᵁ s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert! congr($(Scheme.Hom.congr_app (s2v_l1a_toInvariantSpace_chart f a ha U) (s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Scheme.Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Scheme.Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← CategoryTheory.Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← CategoryTheory.Functor.map_inv, inv_eqToHom]
  simp [← CategoryTheory.Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The canonical invariant-ring map is affine because its composite with the affine structure map is the specified affine map.
Source: Hartshorne, Algebraic Geometry, II.4, affine morphisms and separated diagonals. -/
theorem s2v_l1a_toInvariantSpace_affine :
    IsAffineHom (s2v_l1a_toInvariantSpace f a ha) := by
  have : IsAffineHom (s2v_l1a_invariantSpaceMap f a ha) :=
    s2v_l1a_invariantSpaceMap_affine f a ha
  have : IsAffineHom (s2v_l1a_toInvariantSpace f a ha ≫ s2v_l1a_invariantSpaceMap f a ha) := by
    rw [s2v_l1a_toInvariantSpace_comp_structure]
    infer_instance
  exact IsAffineHom.of_comp _ (s2v_l1a_invariantSpaceMap f a ha)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual invariant-ring inclusion gives a trivial ideal-sheaf kernel for the canonical map.
Source: Stacks Project, tags 04A9 and 01LH, inclusion of invariant rings on affine charts. -/
theorem s2v_l1a_toInvariantSpace_kernel :
    (s2v_l1a_toInvariantSpace f a ha).ker = ⊥ := by
  have : IsAffineHom (s2v_l1a_toInvariantSpace f a ha) :=
    s2v_l1a_toInvariantSpace_affine f a ha
  have : IsAffineHom (s2v_l1a_invariantSpaceMap f a ha) :=
    s2v_l1a_invariantSpaceMap_affine f a ha
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens =>
      ⟨s2v_l1a_invariantSpaceMap f a ha ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U => ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot,
    ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
  simp only [s2v_l1a_toInvariantSpace_app_preimage,
    eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso]
  rw [MorphismProperty.monomorphisms,
    @ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact Subtype.val_injective

end HodgeLean.Foundations.Program
