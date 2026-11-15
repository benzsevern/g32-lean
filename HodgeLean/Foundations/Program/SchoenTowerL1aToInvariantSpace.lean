import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantSpace

/-! # The actual map to the invariant-ring scheme

The morphism induced by inclusions of invariant section rings into the actual
source section rings. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineZariskiSite
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual source map into the scheme of invariant section rings.
Source: Stacks Project, tags 04A9 and 01LH, inclusion of invariant functions and relative affine gluing. -/
def s2v_l1a_toInvariantSpace
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    X ⟶ s2v_l1a_invariantSpace f a ha :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U => (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (s2v_l1a_fixedSectionSubring f a ha U.1).subtype) ≫
      (s2v_l1a_invariantSpaceCover f a ha).f U)
    (fun {U V : Y.AffineZariskiSite} i => by
      have heq : (pullbackRestrictIsoRestrict f U.1).inv ≫
          Scheme.Cover.trans ((directedCover Y).pullback₁ f) i ≫
          (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
            (f.preimage_mono (toOpens_mono i.1.1)) := by
        rw [← cancel_mono (Scheme.Opens.ι _)]
        simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
      rw [← Iso.inv_comp_eq, reassoc_of% heq,
        ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
      dsimp [s2v_l1a_invariantSpaceCover]
      rw [← colimit.w (s2v_l1a_invariantGlueData f a ha).functor i]
      dsimp [s2v_l1a_invariantGlueData, relativeGluingData]
      rw [← Spec.map_comp_assoc]
      rfl)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical morphism restricts to the inclusion of invariant functions on each affine chart.
Source: Stacks Project, tag 01LH, compatibility of relative affine gluing with its charts. -/
@[reassoc]
theorem s2v_l1a_toInvariantSpace_chart
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ s2v_l1a_toInvariantSpace f a ha =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (s2v_l1a_fixedSectionSubring f a ha U.1).subtype) ≫
      (s2v_l1a_invariantSpaceCover f a ha).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ s2v_l1a_toInvariantSpace f a ha
  · congr 1; simp
  delta s2v_l1a_toInvariantSpace
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

/-- The structure morphism on each invariant affine chart is induced by the base section map.
Source: Stacks Project, tag 01LH, the structure map in relative affine gluing. -/
@[reassoc]
theorem s2v_l1a_invariantSpaceMap_chart
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (U : Y.affineOpens) :
    (s2v_l1a_invariantSpaceCover f a ha).f U ≫ s2v_l1a_invariantSpaceMap f a ha =
      Spec.map (CommRingCat.ofHom (s2v_l1a_baseToFixedSections f a ha U.1)) ≫
        U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical invariant-ring morphism factors the specified affine map.
Source: Stacks Project, tags 04A9 and 01LH, inclusion of invariant rings and relative affine gluing. -/
@[reassoc (attr := simp)]
theorem s2v_l1a_toInvariantSpace_comp_structure
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    s2v_l1a_toInvariantSpace f a ha ≫ s2v_l1a_invariantSpaceMap f a ha = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U => ?_
  refine (s2v_l1a_toInvariantSpace_chart_assoc f a ha _ _).trans ?_
  rw [s2v_l1a_invariantSpaceMap_chart, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec =
    (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each specified endomorphism fixes the canonical map to the invariant-ring scheme.
Source: Stacks Project, tag 04A9, the equalizer algebra of invariant functions. -/
theorem s2v_l1a_toInvariantSpace_invariant
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (t : T) :
    a t ≫ s2v_l1a_toInvariantSpace f a ha = s2v_l1a_toInvariantSpace f a ha := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U => ?_
  change (f ⁻¹ᵁ U.1).ι ≫ (a t ≫ s2v_l1a_toInvariantSpace f a ha) =
    (f ⁻¹ᵁ U.1).ι ≫ s2v_l1a_toInvariantSpace f a ha
  have hpre : f ⁻¹ᵁ U.1 ≤ (a t) ⁻¹ᵁ (f ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, ha t]
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (a t) hpre,
    Category.assoc, s2v_l1a_toInvariantSpace_chart,
    ← Category.assoc, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE,
    Category.assoc, Category.assoc, ← Spec.map_comp_assoc]
  congr 2
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact (s2v_l1a_mem_fixedSectionSubring f a ha U.1 s.val).mp s.property t

end HodgeLean.Foundations.Program
