import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! Topological tests on the actual attachment pushout squares.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- Openness on an attachment pushout is tested on its two target pieces.
Source: Mathlib TopCat.isOpen_iff_of_isColimit. -/
lemma c1a5_pushout_isOpen_iff {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (U : Set D) :
    IsOpen U ↔ IsOpen (r ⁻¹' U) ∧ IsOpen (b ⁻¹' U) := by
  constructor
  · intro hU
    exact ⟨hU.preimage r.hom.continuous, hU.preimage b.hom.continuous⟩
  · rintro ⟨hr, hb⟩
    apply (TopCat.isOpen_iff_of_isColimit _ sq.isColimit U).2
    rintro (_ | _ | _)
    · exact hr.preimage t.hom.continuous
    · exact hr
    · exact hb

/-- Continuity on an attachment pushout is tested on its two target pieces.
Source: Mathlib TopCat.continuous_iff_of_isColimit. -/
lemma c1a5_pushout_continuous_iff {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) {X : Type*} [TopologicalSpace X] (f : D → X) :
    Continuous f ↔ Continuous (f ∘ r) ∧ Continuous (f ∘ b) := by
  constructor
  · intro hf
    exact ⟨hf.comp r.hom.continuous, hf.comp b.hom.continuous⟩
  · rintro ⟨hr, hb⟩
    apply (TopCat.continuous_iff_of_isColimit _ sq.isColimit f).2
    rintro (_ | _ | _)
    · exact hr.comp t.hom.continuous
    · exact hr
    · exact hb

/-- Open subspace embeddings remain open subspace embeddings after an attachment pushout.
Source: Mathlib TopCat.isOpen_iff_of_isColimit and type pushout intersection classification. -/
lemma c1a5_pushout_isOpenEmbedding {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Topology.IsOpenEmbedding l) :
    Topology.IsOpenEmbedding r := by
  let F := forget TopCat.{0}
  have sq' := sq.map F
  have hlm : Mono (F.map l) := (mono_iff_injective _).2 hl.injective
  have hrm : Mono (F.map r) :=
    (MorphismProperty.monomorphisms (Type)).of_isPushout sq' hlm
  have hr : Function.Injective r := (mono_iff_injective _).1 hrm
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap r.hom.continuous hr
  intro U hU
  apply (c1a5_pushout_isOpen_iff sq (r '' U)).2
  constructor
  · rwa [Set.preimage_image_eq U hr]
  · have hs : b ⁻¹' (r '' U) = l '' (t ⁻¹' U) := by
      ext c
      constructor
      · rintro ⟨d, hd, hde⟩
        obtain ⟨a, hal, hat⟩ :=
          (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sq'.flip.isColimit
            hl.injective c d).1 hde.symm
        refine ⟨a, ?_, hal⟩
        change t a ∈ U
        rw [show t a = d from hat]
        exact hd
      · rintro ⟨a, ha, rfl⟩
        exact ⟨t a, ha, ConcreteCategory.congr_hom sq.w a⟩
    rw [hs]
    exact hl.isOpenMap _ (hU.preimage t.hom.continuous)

/-- A pushout identifies no distinct points away from the attaching image in its right piece.
Source: the type-valued universal property of the underlying topological pushout. -/
lemma c1a5_pushout_right_injOn_complement {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) : Set.InjOn b (Set.range l)ᶜ := by
  classical
  intro x hx y hy hxy
  let F := forget TopCat.{0}
  let u : F.obj B ⟶ F.obj C := ↾fun _ ↦ x
  let v : F.obj C ⟶ F.obj C := ↾fun z ↦ if z ∈ Set.range l then x else z
  have hw : F.map t ≫ u = F.map l ≫ v := by
    ext a
    change x = if l a ∈ Set.range l then x else l a
    rw [if_pos (show l a ∈ Set.range l from ⟨a, rfl⟩)]
  let d := (sq.map F).desc u v hw
  have he (z : C) (hz : z ∉ Set.range l) : d (b z) = z := by
    have h := ConcreteCategory.congr_hom ((sq.map F).inr_desc u v hw) z
    change d (b z) = if z ∈ Set.range l then x else z at h
    rwa [if_neg hz] at h
  exact (he x hx).symm.trans ((congrArg d hxy).trans (he y hy))

/-- The two target-piece images meet exactly along the attaching image.
Source: Mathlib Types.pushoutCocone_inl_eq_inr_iff_of_isColimit. -/
lemma c1a5_pushout_preimage_left_range {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l) :
    b ⁻¹' Set.range r = Set.range l := by
  ext c
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨a, hal, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit (sq.map (forget TopCat)).flip.isColimit
        hl c d).1 hd.symm
    exact ⟨a, hal⟩
  · rintro ⟨a, rfl⟩
    exact ⟨t a, ConcreteCategory.congr_hom sq.w a⟩

end HodgeLean.Foundations.Program
