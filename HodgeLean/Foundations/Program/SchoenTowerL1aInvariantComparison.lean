import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantDominant
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantSectionMaps
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Comparison of the actual invariant-ring scheme with a categorical quotient

The universal property supplies a section, and the trivial ideal-sheaf kernel makes it
an isomorphism. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- A categorical quotient with affine quotient map is its actual invariant-ring scheme.
Source: Stacks Project, tags 04A9 and 01LH; Hartshorne, Algebraic Geometry, II.4, sections of separated morphisms. -/
theorem s2v_l1a_invariantSpaceMap_isIso
    {S : Scheme.{0}} (X Y : Over S)
    {T : Type*} [Finite T] (f : X ⟶ Y) [IsAffineHom f.left]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (hcat : ∀ (W : Over S) (g : X ⟶ W),
      (∀ t, a t ≫ g = g) → ∃! u : Y ⟶ W, f ≫ u = g) :
    IsIso (s2v_l1a_invariantSpaceMap f.left (fun t => (a t).left)
      (fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t))) := by
  let a' := fun t => (a t).left
  let ha' : ∀ t, a' t ≫ f.left = f.left :=
    fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)
  let Q := s2v_l1a_invariantSpace f.left a' ha'
  let r : Q ⟶ Y.left := s2v_l1a_invariantSpaceMap f.left a' ha'
  let q : X.left ⟶ Q := s2v_l1a_toInvariantSpace f.left a' ha'
  let Qs : Over S := Over.mk (r ≫ Y.hom)
  let qs : X ⟶ Qs := Over.homMk q (by
    change q ≫ (r ≫ Y.hom) = X.hom
    dsimp [q, r]
    rw [← Category.assoc, s2v_l1a_toInvariantSpace_comp_structure]
    exact f.w)
  have hqs : ∀ t, a t ≫ qs = qs := by
    intro t
    apply Over.OverMorphism.ext
    exact s2v_l1a_toInvariantSpace_invariant f.left a' ha' t
  obtain ⟨g, hg, hgu⟩ := hcat Qs qs hqs
  let rs : Qs ⟶ Y := Over.homMk r
  have hgr : g ≫ rs = 𝟙 Y := by
    apply (hcat Y f ha).unique
    · rw [← Category.assoc, hg]
      apply Over.OverMorphism.ext
      exact s2v_l1a_toInvariantSpace_comp_structure f.left a' ha'
    · simp
  have hgr' : g.left ≫ r = 𝟙 Y.left :=
    congrArg (fun k : Y ⟶ Y => k.left) hgr
  have : IsAffineHom r := s2v_l1a_invariantSpaceMap_affine f.left a' ha'
  have : IsClosedImmersion (g.left ≫ r) := by rw [hgr']; infer_instance
  have : IsClosedImmersion g.left := IsClosedImmersion.of_comp g.left r
  have heq : f.left ≫ g.left = q := congrArg (fun k : X ⟶ Qs => k.left) hg
  have hgker : g.left.ker = ⊥ := by
    apply le_bot_iff.mp
    apply (f.left.le_ker_comp g.left).trans
    rw [heq, s2v_l1a_toInvariantSpace_kernel]
  have : IsIso g.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hgker
  have hr : r = inv g.left := by
    rw [← cancel_epi g.left, hgr', IsIso.hom_inv_id]
  change IsIso r
  rw [hr]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If the invariant-ring structure map is invertible, the actual base section map is invertible on every affine.
Source: Stacks Project, tag 01LH, the cartesian affine charts of relative affine gluing. -/
theorem s2v_l1a_baseToFixedSections_isIso
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    [IsIso (s2v_l1a_invariantSpaceMap f a ha)] (U : Y.affineOpens) :
    IsIso (CommRingCat.ofHom (s2v_l1a_baseToFixedSections f a ha U.1)) := by
  let b := CommRingCat.ofHom (s2v_l1a_baseToFixedSections f a ha U.1)
  have : IsIso (s2v_l1a_invariantGlueData f a ha).toBase :=
    inferInstanceAs (IsIso (s2v_l1a_invariantSpaceMap f a ha))
  have hi := ((s2v_l1a_invariantGlueData f a ha).isPullback_natTrans_ι_toBase U).isIso_fst_of_isIso
  change IsIso (Spec.map b ≫ U.2.isoSpec.inv) at hi
  have : IsIso (Spec.map b) := IsIso.of_isIso_comp_right _ U.2.isoSpec.inv
  have : IsIso b.op := (isIso_iff_of_reflects_iso b.op Scheme.Spec).mp this
  exact isIso_of_op b

/-- On each affine target open of the specified categorical quotient, section pullback identifies the base ring with the actual invariant subring.
Source: Stacks Project, tags 04A9 and 01LH, invariant rings and relative affine gluing. -/
theorem s2v_l1a_affine_sections_image_of_categorical_quotient
    {S : Scheme.{0}} (X Y : Over S)
    {T : Type*} [Finite T] (f : X ⟶ Y) [IsAffineHom f.left]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (hcat : ∀ (W : Over S) (g : X ⟶ W),
      (∀ t, a t ≫ g = g) → ∃! u : Y ⟶ W, f ≫ u = g)
    (U : Y.left.affineOpens) :
    Function.Bijective (s2v_l1a_baseToFixedSections f.left (fun t => (a t).left)
      (fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)) U.1) := by
  have := s2v_l1a_invariantSpaceMap_isIso X Y f a ha hcat
  have := s2v_l1a_baseToFixedSections_isIso f.left (fun t => (a t).left)
    (fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)) U
  exact ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (s2v_l1a_baseToFixedSections f.left (fun t => (a t).left)
      (fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)) U.1))

/-- Pullback over an affine target open is injective and its image consists exactly of sections fixed by the specified endomorphisms.
Source: Stacks Project, tags 04A9 and 01LH, invariant rings and relative affine gluing. -/
theorem s2v_l1a_affine_sections_range_of_categorical_quotient
    {S : Scheme.{0}} (X Y : Over S)
    {T : Type*} [Finite T] (f : X ⟶ Y) [IsAffineHom f.left]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (hcat : ∀ (W : Over S) (g : X ⟶ W),
      (∀ t, a t ≫ g = g) → ∃! u : Y ⟶ W, f ≫ u = g)
    (U : Y.left.affineOpens) :
    Function.Injective (f.left.app U.1).hom ∧
      ∀ s : Γ(X.left, f.left ⁻¹ᵁ U.1),
        s ∈ Set.range (f.left.app U.1).hom ↔
          ∀ t, (s2v_l1a_saturatedSectionEnd f.left (fun t => (a t).left)
            (fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)) U.1 t).hom s = s := by
  let a' := fun t => (a t).left
  let ha' := fun t => congrArg (fun g : X ⟶ Y => g.left) (ha t)
  let b := s2v_l1a_baseToFixedSections f.left a' ha' U.1
  have hb : Function.Bijective b :=
    s2v_l1a_affine_sections_image_of_categorical_quotient X Y f a ha hcat U
  constructor
  · intro x y hxy
    apply hb.1
    exact Subtype.ext hxy
  · intro s
    rw [← s2v_l1a_mem_fixedSectionSubring f.left a' ha' U.1 s]
    constructor
    · rintro ⟨x, rfl⟩
      exact (b x).property
    · intro hs
      obtain ⟨x, hx⟩ := hb.2 ⟨s, hs⟩
      exact ⟨x, congrArg Subtype.val hx⟩

end HodgeLean.Foundations.Program
