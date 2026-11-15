import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachedCollarHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5PushoutComplementHelpers

/-! The neighborhood and complement cover of an actual cell attachment.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The attached base has closed image whenever the attaching subspace has closed image.
Source: the final topology of the actual pushout and its image intersection formula. -/
lemma c1a5_pushout_left_range_isClosed {A B C D : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) (hl : Function.Injective l)
    (hc : IsClosed (Set.range l)) : IsClosed (Set.range r) := by
  rw [← isOpen_compl_iff]
  apply (c1a5_pushout_isOpen_iff sq _).2
  constructor
  · have h : r ⁻¹' (Set.range r)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range_self, not_true_eq_false,
        Set.mem_empty_iff_false]
    rw [h]
    exact isOpen_empty
  · rw [Set.preimage_compl, c1a5_pushout_preimage_left_range sq hl]
    exact hc.isOpen_compl

/-- The attached collar image contains the actual attached base.
Source: the defining pushout descent of the neighborhood map. -/
lemma c1a5_attached_collar_contains_base {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) :
    Set.range r ⊆ Set.range (c1a5_attached_collar_map sq) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨pushout.inl t j x, ?_⟩
  exact ConcreteCategory.congr_hom
    ((IsPushout.of_hasPushout t j).inl_desc r (k ≫ b) _) x

/-- The cell map pulls the attached neighborhood back to the original cell neighborhood.
Source: the actual neighborhood pushout and the pushout image intersection formula. -/
lemma c1a5_attached_collar_preimage {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hk : Function.Injective k) :
    b ⁻¹' Set.range (c1a5_attached_collar_map sq) = Set.range k :=
  c1a5_pushout_preimage_left_range (c1a5_attached_collar_square sq) hk

/-- The attached neighborhood and the complement of the attached base cover the attachment.
Source: Hatcher §2.1, Theorem 2.20, neighborhood excision cover. -/
lemma c1a5_attached_collar_cover {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) :
    Set.range (c1a5_attached_collar_map sq) ∪ (Set.range r)ᶜ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Set.range r
  · exact Or.inl (c1a5_attached_collar_contains_base sq hx)
  · exact Or.inr hx

end HodgeLean.Foundations.Program
