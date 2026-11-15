import HodgeLean.Foundations.Program.SchoenTransferC1a5PushoutTopologyHelpers
import Mathlib.Topology.Homeomorph.Lemmas

/-! Complement identifications for actual attachment pushouts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The unattached part of a cell piece maps into the complement of the attached base.
Source: the underlying pushout intersection classification. -/
def c1a5_pushout_complement_map {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l) :
    TopCat.of ((Set.range l)ᶜ : Set C) ⟶ TopCat.of ((Set.range r)ᶜ : Set D) :=
  TopCat.ofHom
    { toFun x := ⟨b x.val, by
        intro hx
        exact x.property (Eq.mp
          (congrArg (fun S : Set C ↦ x.val ∈ S) (c1a5_pushout_preimage_left_range sq hl)) hx)⟩
      continuous_toFun := (b.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

example := @c1a5_pushout_complement_map

/-- The actual attachment complement map is bijective.
Source: Mathlib Types.eq_or_eq_of_isPushout' and injectivity away from the attaching image. -/
lemma c1a5_pushout_complement_map_bijective {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l) :
    Function.Bijective (c1a5_pushout_complement_map sq hl) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact c1a5_pushout_right_injOn_complement sq x.property y.property (congrArg Subtype.val h)
  · intro z
    obtain ⟨d, hd⟩ | ⟨c, hc, hca⟩ :=
      Types.eq_or_eq_of_isPushout' (sq.map (forget TopCat)) z.val
    · exact (z.property ⟨d, hd⟩).elim
    · exact ⟨⟨c, hca⟩, Subtype.ext hc⟩

/-- The complement map is open when the attaching image is a closed subspace.
Source: the final topology of a pushout and its complement intersection classification. -/
lemma c1a5_pushout_complement_map_isOpenMap {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l)
    (hc : IsClosed (Set.range l)) :
    IsOpenMap (c1a5_pushout_complement_map sq hl) := by
  have hb : IsOpenMap (fun x : ((Set.range l)ᶜ : Set C) ↦ b x.val) := by
    intro S hS
    let W : Set C := Subtype.val '' S
    have hW : IsOpen W := hc.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap S hS
    have hWc : W ⊆ (Set.range l)ᶜ := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    have hpre : b ⁻¹' (b '' W) = W := by
      apply Set.Subset.antisymm
      · rintro x ⟨y, hy, he⟩
        have hyc := hWc hy
        have hxc : x ∈ (Set.range l)ᶜ := by
          intro hx
          have hby : b y ∈ Set.range r := by
            rw [he]
            change x ∈ b ⁻¹' Set.range r
            rw [c1a5_pushout_preimage_left_range sq hl]
            exact hx
          apply hyc
          have hm : y ∈ b ⁻¹' Set.range r := hby
          rw [c1a5_pushout_preimage_left_range sq hl] at hm
          exact hm
        have hxy := c1a5_pushout_right_injOn_complement sq hyc hxc he
        exact hxy ▸ hy
      · intro x hx
        exact ⟨x, hx, rfl⟩
    have hr : r ⁻¹' (b '' W) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro d ⟨c, hcW, he⟩
      apply hWc hcW
      have hbc : b c ∈ Set.range r := ⟨d, he.symm⟩
      have hm : c ∈ b ⁻¹' Set.range r := hbc
      rw [c1a5_pushout_preimage_left_range sq hl] at hm
      exact hm
    have hopen : IsOpen (b '' W) := (c1a5_pushout_isOpen_iff sq _).mpr
      ⟨by rw [hr]; exact isOpen_empty, by rw [hpre]; exact hW⟩
    convert hopen using 1
    ext d
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  exact hb.codRestrict _

/-- Removing the attached base identifies the actual pushout with the unattached cell part.
Source: the pushout final topology and its complement bijection. -/
def c1a5_pushout_complement_homeomorph {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l)
    (hc : IsClosed (Set.range l)) :
    ((Set.range l)ᶜ : Set C) ≃ₜ ((Set.range r)ᶜ : Set D) :=
  (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (c1a5_pushout_complement_map sq hl).hom.continuous
    (c1a5_pushout_complement_map_bijective sq hl).injective
    (c1a5_pushout_complement_map_isOpenMap sq hl hc)).toIsEmbedding.toHomeomorphOfSurjective
      (c1a5_pushout_complement_map_bijective sq hl).surjective

example := @c1a5_pushout_complement_homeomorph

end HodgeLean.Foundations.Program
