import HodgeLean.Foundations.Program.SchoenTransferC1a5PushoutHomotopyHelpers

/-! Open neighborhoods in actual cell attachment pushouts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The attached neighborhood maps into the full attachment through the given actual pushout.
Source: Mathlib IsPushout.desc and IsPushout.of_top'. -/
def c1a5_attached_collar_map {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) : pushout t j ⟶ D :=
  (IsPushout.of_hasPushout t j).desc r (k ≫ b) (by rw [sq.w, Category.assoc])

example := @c1a5_attached_collar_map

/-- The neighborhood-to-attachment square is itself the actual pushout of the open inclusion.
Source: Mathlib IsPushout.of_top'. -/
lemma c1a5_attached_collar_square {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) :
    IsPushout (pushout.inr t j) k (c1a5_attached_collar_map sq) b :=
  sq.of_top' (IsPushout.of_hasPushout t j)

/-- The attached collar is an open subspace of the full attachment.
Source: the actual collar pushout square and preservation of open embeddings by pushouts. -/
lemma c1a5_attached_collar_isOpenEmbedding {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hk : Topology.IsOpenEmbedding k) :
    Topology.IsOpenEmbedding (c1a5_attached_collar_map sq) :=
  c1a5_pushout_isOpenEmbedding (c1a5_attached_collar_square sq) hk

/-- A boundary-neighborhood retraction extends to a retraction of the attached neighborhood
onto the attached base.
Source: Mathlib IsPushout.desc, applied to the given geometric retraction. -/
def c1a5_attached_collar_retract {A B U : TopCat.{0}}
    (t : A ⟶ B) (j : A ⟶ U) (q : U ⟶ A) (hq : j ≫ q = 𝟙 A) :
    pushout t j ⟶ B :=
  (IsPushout.of_hasPushout t j).desc (𝟙 B) (q ≫ t) (by
    rw [← Category.assoc, hq, Category.id_comp, Category.comp_id])

example := @c1a5_attached_collar_retract

/-- The attached neighborhood retraction is the identity on the attached base.
Source: Mathlib IsPushout.inl_desc. -/
@[reassoc]
lemma c1a5_attached_collar_retract_inl {A B U : TopCat.{0}}
    (t : A ⟶ B) (j : A ⟶ U) (q : U ⟶ A) (hq : j ≫ q = 𝟙 A) :
    pushout.inl t j ≫ c1a5_attached_collar_retract t j q hq = 𝟙 B := by
  exact (IsPushout.of_hasPushout t j).inl_desc _ _ _

/-- The attached neighborhood retraction restricts to the given collar retraction.
Source: Mathlib IsPushout.inr_desc. -/
@[reassoc]
lemma c1a5_attached_collar_retract_inr {A B U : TopCat.{0}}
    (t : A ⟶ B) (j : A ⟶ U) (q : U ⟶ A) (hq : j ≫ q = 𝟙 A) :
    pushout.inr t j ≫ c1a5_attached_collar_retract t j q hq = q ≫ t := by
  exact (IsPushout.of_hasPushout t j).inr_desc _ _ _

/-- A collar deformation fixing the boundary extends across the attached base.
Source: Hatcher §2.1, homotopy gluing on an attachment pushout. -/
def c1a5_attached_collar_homotopy {A B U : TopCat.{0}}
    (t : A ⟶ B) (j : A ⟶ U) (q : U ⟶ A) (hq : j ≫ q = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (hfixed : ∀ (s : unitInterval) (a : A), H (s, j a) = j a) :
    TopCat.Homotopy (𝟙 (pushout t j))
      (c1a5_attached_collar_retract t j q hq ≫ pushout.inl t j) := by
  let i := pushout.inl t j
  let u := pushout.inr t j
  let ret := c1a5_attached_collar_retract t j q hq
  have hi : i ≫ ret = 𝟙 B := c1a5_attached_collar_retract_inl t j q hq
  have hu : u ≫ ret = q ≫ t := c1a5_attached_collar_retract_inr t j q hq
  let HB : TopCat.Homotopy (i ≫ 𝟙 _) (i ≫ (ret ≫ i)) :=
    { toFun := fun p ↦ i p.2
      continuous_toFun := i.hom.continuous.comp continuous_snd
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ by
        exact (ConcreteCategory.congr_hom
          (by rw [← Category.assoc, hi, Category.id_comp] : i ≫ (ret ≫ i) = i) x).symm }
  let HC : TopCat.Homotopy (u ≫ 𝟙 _) (u ≫ (ret ≫ i)) :=
    { toFun := fun p ↦ u (H p)
      continuous_toFun := u.hom.continuous.comp H.continuous
      map_zero_left := fun x ↦ congrArg u (H.map_zero_left x)
      map_one_left := fun x ↦ by
        have hw : (q ≫ j) ≫ u = u ≫ (ret ≫ i) := by
          rw [← Category.assoc, hu, Category.assoc]
          exact congrArg (fun v ↦ q ≫ v) (pushout.condition (f := t) (g := j)).symm
        exact (congrArg u (H.map_one_left x)).trans
          (ConcreteCategory.congr_hom hw x) }
  exact c1a5_pushout_homotopy (IsPushout.of_hasPushout t j) HB HC (by
    intro s a
    change i (t a) = u (H (s, j a))
    rw [hfixed]
    exact ConcreteCategory.congr_hom (pushout.condition (f := t) (g := j)) a)

example := @c1a5_attached_collar_homotopy

end HodgeLean.Foundations.Program
