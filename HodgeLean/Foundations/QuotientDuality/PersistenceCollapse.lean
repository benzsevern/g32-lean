import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions.SumProd

/-! Collapse spaces for actual pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The equivalence relation identifying all points of the specified subset. -/
def persistenceCollapseSetoid {X : Type*} (A : Set X) : Setoid X where
  r x y := x = y ∨ x ∈ A ∧ y ∈ A
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      rintro x y z (rfl | ⟨hx, hy⟩) hz
      · exact hz
      · rcases hz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩ }

/-- The map on collapse spaces induced by the literal ambient map. -/
def persistenceCollapseMap {X Y : Type*} (f : X → Y) (A : Set Y) :
    Quotient (persistenceCollapseSetoid (f ⁻¹' A)) →
      Quotient (persistenceCollapseSetoid A) :=
  Quotient.map f (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, hy⟩)

lemma persistence_collapse_eq_iff {X : Type*} (A : Set X) (x y : X) :
    Quotient.mk (persistenceCollapseSetoid A) x =
      Quotient.mk (persistenceCollapseSetoid A) y ↔ x = y ∨ x ∈ A ∧ y ∈ A :=
  Quotient.eq

lemma persistence_collapse_isClosedMap {X : Type*} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A) :
    IsClosedMap (Quotient.mk (persistenceCollapseSetoid A)) := by
  let q := Quotient.mk (persistenceCollapseSetoid A)
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  intro C hC
  apply hq.isCoinducing.isClosed_preimage.mp
  by_cases h : ∃ z, z ∈ C ∧ z ∈ A
  · have heq : q ⁻¹' (q '' C) = C ∪ A := by
      ext x
      constructor
      · rintro ⟨z, hz, heq⟩
        rcases (persistence_collapse_eq_iff A z x).mp heq with rfl | ⟨_, hx⟩
        · exact Or.inl hz
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · obtain ⟨z, hzC, hzA⟩ := h
          exact ⟨z, hzC, (persistence_collapse_eq_iff A z x).mpr
            (Or.inr ⟨hzA, hx⟩)⟩
    rw [heq]
    exact hC.union hA
  · have heq : q ⁻¹' (q '' C) = C := by
      ext x
      constructor
      · rintro ⟨z, hz, heq⟩
        rcases (persistence_collapse_eq_iff A z x).mp heq with rfl | ⟨hzA, _⟩
        · exact hz
        · exact (h ⟨z, hz, hzA⟩).elim
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact hC

lemma persistence_collapse_map_bijective {X Y : Type*} (f : X → Y) (A : Set Y)
    (hB : (f ⁻¹' A).Nonempty)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) :
    Function.Bijective (persistenceCollapseMap f A) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h x =>
      induction b using Quotient.inductionOn with | h y =>
        intro hxy
        apply Quotient.sound
        rcases (persistence_collapse_eq_iff A (f x) (f y)).mp hxy with hxy | hxy
        · by_cases hx : f x ∈ A
          · exact Or.inr ⟨hx, by change f y ∈ A; rw [← hxy]; exact hx⟩
          · obtain ⟨z, hz, hu⟩ := hfibre (f x) hx
            exact Or.inl ((hu x rfl).trans (hu y hxy.symm).symm)
        · exact Or.inr hxy
  · intro a
    induction a using Quotient.inductionOn with | h y =>
      by_cases hy : y ∈ A
      · obtain ⟨x, hx⟩ := hB
        refine ⟨Quotient.mk _ x, ?_⟩
        exact Quotient.sound (Or.inr ⟨hx, hy⟩)
      · obtain ⟨x, hx, _⟩ := hfibre y hy
        refine ⟨Quotient.mk _ x, ?_⟩
        exact Quotient.sound (Or.inl hx)

lemma persistence_collapse_map_isHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hclosed : IsClosedMap f)
    (A : Set Y) (hA : IsClosed A) (hB : (f ⁻¹' A).Nonempty)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) :
    IsHomeomorph (persistenceCollapseMap f A) := by
  let qX := Quotient.mk (persistenceCollapseSetoid (f ⁻¹' A))
  let qY := Quotient.mk (persistenceCollapseSetoid A)
  have hbij := persistence_collapse_map_bijective f A hB hfibre
  have hqX : IsQuotientMap qX := isQuotientMap_quotient_mk'
  have hqY : Continuous qY := continuous_quotient_mk'
  have hsurj : Function.Surjective (qY ∘ f) := by
    exact hbij.surjective.comp hqX.surjective
  have hquot : IsQuotientMap (qY ∘ f) :=
    ((persistence_collapse_isClosedMap A hA).comp hclosed).isQuotientMap
      (hqY.comp hf) hsurj
  have hmap : IsQuotientMap (persistenceCollapseMap f A) :=
    IsQuotientMap.of_comp_of_isCoinducing (f := qX)
      (g := persistenceCollapseMap f A) hquot hqX.isCoinducing
  exact isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hmap, hbij.injective⟩

end HodgeLean.Foundations.QuotientDuality
