import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentCoverHelpers

/-! Identifying the actual overlaps in attachment neighborhood covers.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The attachment complement homeomorphism restricts to the neighborhood-cover overlaps.
Source: Hatcher §2.1, Theorem 2.20, together with the actual collar preimage formula. -/
def c1a5_pushout_collar_overlap_homeomorph {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hl : Function.Injective (j ≫ k))
    (hc : IsClosed (Set.range (j ≫ k))) (hk : Function.Injective k) :
    {x : ((Set.range (j ≫ k))ᶜ : Set C) // x.val ∈ Set.range k} ≃ₜ
      {y : ((Set.range r)ᶜ : Set D) // y.val ∈ Set.range (c1a5_attached_collar_map sq)} :=
  (c1a5_pushout_complement_homeomorph sq hl hc).subtype (by
    intro x
    change x.val ∈ Set.range k ↔ b x.val ∈ Set.range (c1a5_attached_collar_map sq)
    exact (Set.ext_iff.mp (c1a5_attached_collar_preimage sq hk) x.val).symm)

example := @c1a5_pushout_collar_overlap_homeomorph

/-- The overlap homeomorphism and complement homeomorphism commute with the actual inclusions.
Source: the subtype restriction of the actual attachment complement map. -/
lemma c1a5_pushout_collar_overlap_naturality {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hl : Function.Injective (j ≫ k))
    (hc : IsClosed (Set.range (j ≫ k))) (hk : Function.Injective k)
    (x : {x : ((Set.range (j ≫ k))ᶜ : Set C) // x.val ∈ Set.range k}) :
    (c1a5_pushout_collar_overlap_homeomorph sq hl hc hk x).val =
      c1a5_pushout_complement_homeomorph sq hl hc x.val := rfl

end HodgeLean.Foundations.Program
